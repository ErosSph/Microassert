# Normalize Jasper's overlapping list queries by native CID + checker_status.
# This merges repeated coverage-item queries, NOT assertion bodies or labels.
set mutation_items_by_cid [dict create]
set mutation_export [open {mutation_items.tsv} w]
foreach query_status {covered_and_checked uncovered_or_unchecked unreachable_or_undetectable unprocessed} {
    foreach item [check_cov -list -status $query_status -silent] {
        puts $mutation_export "$query_status\t$item"
        if {![dict exists $item cid] || ![dict exists $item checker_status]} {
            close $mutation_export
            error {Native mutation item lacks CID/checker_status; refusing guessed coverage}
        }
        set cid [dict get $item cid]
        set outcome [string tolower [dict get $item checker_status]]
        switch -- $outcome {
            checked {set normalized checked}
            unchecked {set normalized unchecked}
            undetectable - unreachable {set normalized undetectable}
            unprocessed {set normalized unprocessed}
            default {
                close $mutation_export
                error "Unsupported native checker status: $outcome"
            }
        }
        set kind [string tolower [dict get $item cover_item_type]]
        set record [list $normalized $kind]
        if {[dict exists $mutation_items_by_cid $cid] && [dict get $mutation_items_by_cid $cid] ne $record} {
            close $mutation_export
            error "Inconsistent repeated native CID: $cid"
        }
        dict set mutation_items_by_cid $cid $record
    }
}
close $mutation_export
set mutation_counts [dict create]
set mutation_types {all branch statement expression toggle functional}
foreach kind $mutation_types {
    foreach outcome {checked unchecked undetectable unprocessed} {
        dict set mutation_counts "$kind,$outcome" 0
    }
}
dict for {cid record} $mutation_items_by_cid {
    lassign $record outcome kind
    if {$kind ni $mutation_types || $kind eq "all"} {
        error "Unsupported native cover item type: $kind"
    }
    dict incr mutation_counts "all,$outcome"
    dict incr mutation_counts "$kind,$outcome"
}
set mutation_summary [open {mutation_effective.tsv} w]
puts $mutation_summary "type\tchecked\tunchecked\tundetectable\tunprocessed\traw_total\teffective_denominator\traw_percent\teffective_percent"
set mutation_text [open {mutation_effective_report.txt} w]
puts $mutation_text {JasperGold native mutation: 28800s (8h) measurement budget.}
puts $mutation_text {Effective = Checked / (Total - native Undetectable). Genuine Unprocessed remains in the denominator.}
puts $mutation_text {When Unprocessed=0, this equals Checked/(Checked+Unchecked), the previous report convention.}
puts $mutation_text {This is a COI-conditioned checker metric, not full-design fault-detection accuracy.}
puts $mutation_text {Original assertions with CEX/unresolved results are retained; inspect baseline_formal_report.txt and native eligibility diagnostics.}
foreach kind $mutation_types {
    set checked [dict get $mutation_counts "$kind,checked"]
    set unchecked [dict get $mutation_counts "$kind,unchecked"]
    set undetectable [dict get $mutation_counts "$kind,undetectable"]
    set unprocessed [dict get $mutation_counts "$kind,unprocessed"]
    set total [expr {$checked + $unchecked + $undetectable + $unprocessed}]
    set denominator [expr {$total - $undetectable}]
    set raw_percent N/A
    set effective_percent N/A
    if {$total > 0} {set raw_percent [format %.4f [expr {100.0 * $checked / $total}]]}
    if {$denominator > 0} {set effective_percent [format %.4f [expr {100.0 * $checked / $denominator}]]}
    puts $mutation_summary "$kind\t$checked\t$unchecked\t$undetectable\t$unprocessed\t$total\t$denominator\t$raw_percent\t$effective_percent"
    puts $mutation_text "$kind: effective $checked/$denominator = $effective_percent%; raw $checked/$total = $raw_percent%; undetectable=$undetectable; unprocessed=$unprocessed"
    if {$kind eq "all"} {
        puts "NATIVE_MUTATION_EFFECTIVE checked=$checked denominator=$denominator percent=$effective_percent raw_total=$total undetectable=$undetectable unprocessed=$unprocessed"
    }
}
close $mutation_summary
close $mutation_text
