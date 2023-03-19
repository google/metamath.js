include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cbs.mm"
include "crefld.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cds.mm"
include "cr.mm"
include "cmap.mm"
include "id.mm"
include "eqid.mm"
include "rrxbasefi.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqtr2d.mm"
include "adantr.mm"
include "w3a.mm"
include "ccnfld.mm"
include "cress.mm"
include "df-refld.mm"
include "oveq1i.mm"
include "simp1.mm"
include "wa.mm"
include "wf.mm"
include "simpr.mm"
include "eleqtrd.mm"
include "3adant3.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "3adant2.mm"
include "resubcld.mm"
include "resqcld.mm"
include "regsumfsum.mm"
include "eqtrd.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "3expb.mm"
include "mpt2eq123dva.mm"
include "rrxds.mm"

theorem rrxdsfi
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cH: class H
  let cI: class I
  let vx: setvar x
  assume rrxdsfi.h: |- H = ( RR^ ` I )
  assume rrxdsfi.b: |- B = ( RR ^m I )

  disjoint B k
  disjoint H f
  disjoint H g
  disjoint H k
  disjoint f g
  disjoint f k
  disjoint g k
  disjoint I f
  disjoint I g
  disjoint I k
  disjoint k x
  assert |- ( I e. Fin -> ( dist ` H ) = ( f e. B , g e. B |-> ( sqrt ` sum_ k e. I ( ( ( f ` k ) - ( g ` k ) ) ^ 2 ) ) ) )

  proof
    cI
    cfn
    wcel
    #
    vf
    vg
    cB
    cB
    cI
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    @1
    vg
    cv
    #
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    cmpt2
    vf
    vg
    cH
    cbs
    cfv
    #
    @10
    crefld
    vk
    cI
    @7
    cmpt
    #
    cgsu
    co
    #
    csqrt
    cfv
    #
    cmpt2
    cH
    cds
    cfv
    @0
    vf
    vg
    cB
    cB
    @9
    @10
    @10
    @13
    @0
    @10
    cr
    cI
    cmap
    co
    #
    cB
    @0
    @10
    cH
    cI
    @0
    id
    rrxdsfi.h
    @10
    eqid
    #
    rrxbasefi
    @14
    cB
    wceq
    @0
    cB
    @14
    rrxdsfi.b
    eqcomi
    a1i
    eqtr2d
    #
    @0
    cB
    @10
    wceq
    @2
    cB
    wcel
    #
    @16
    adantr
    @0
    @17
    @4
    cB
    wcel
    #
    @9
    @13
    wceq
    @0
    @17
    @18
    w3a
    #
    @8
    @12
    csqrt
    @19
    @12
    @8
    @19
    @12
    ccnfld
    cr
    cress
    co
    #
    @11
    cgsu
    co
    #
    @8
    @12
    @21
    wceq
    @19
    crefld
    @20
    @11
    cgsu
    df-refld
    oveq1i
    a1i
    @19
    cI
    @7
    vk
    @0
    @17
    @18
    simp1
    @19
    @1
    cI
    wcel
    wa
    #
    @6
    @22
    @3
    @5
    @19
    cI
    cr
    @1
    @2
    @19
    @2
    @14
    wcel
    #
    cI
    cr
    @2
    wf
    @0
    @17
    @23
    @18
    @0
    @17
    wa
    #
    @2
    cB
    @14
    @0
    @17
    simpr
    cB
    @14
    wceq
    #
    @24
    rrxdsfi.b
    a1i
    eleqtrd
    3adant3
    @2
    cr
    cI
    elmapi
    syl
    ffvelrnda
    @19
    cI
    cr
    @1
    @4
    @19
    @4
    @14
    wcel
    #
    cI
    cr
    @4
    wf
    @0
    @18
    @26
    @17
    @0
    @18
    wa
    #
    @4
    cB
    @14
    @0
    @18
    simpr
    @25
    @27
    rrxdsfi.b
    a1i
    eleqtrd
    3adant2
    @4
    cr
    cI
    elmapi
    syl
    ffvelrnda
    resubcld
    resqcld
    regsumfsum
    eqtrd
    eqcomd
    fveq2d
    3expb
    mpt2eq123dva
    vk
    @10
    vf
    vg
    cH
    cI
    cfn
    rrxdsfi.h
    @15
    rrxds
    eqtr2d
end
