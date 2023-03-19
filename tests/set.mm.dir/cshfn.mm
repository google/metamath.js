include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "cz.mm"
include "c0.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cmo.mm"
include "cop.mm"
include "csubstr.mm"
include "cconcat.mm"
include "cif.mm"
include "ccsh.mm"
include "wa.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "simpl.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "opeq12d.mm"
include "opeq2d.mm"
include "ifbieq2d.mm"
include "df-csh.mm"
include "0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "ovmpt2a.mm"

theorem cshfn
  let vf: setvar f
  let cN: class N
  let cW: class W
  let vl: setvar l
  let vn: setvar n
  let vw: setvar w

  disjoint f l
  disjoint N n
  disjoint N w
  disjoint n w
  disjoint W n
  disjoint W w
  disjoint f n
  disjoint f w
  disjoint l n
  disjoint l w
  assert |- ( ( W e. { f | E. l e. NN0 f Fn ( 0 ..^ l ) } /\ N e. ZZ ) -> ( W cyclShift N ) = if ( W = (/) , (/) , ( ( W substr <. ( N mod ( # ` W ) ) , ( # ` W ) >. ) ++ ( W substr <. 0 , ( N mod ( # ` W ) ) >. ) ) ) )

  proof
    vw
    vn
    cW
    cN
    vf
    cv
    cc0
    vl
    cv
    cfzo
    co
    wfn
    vl
    cn0
    wrex
    vf
    cab
    cz
    vw
    cv
    #
    c0
    wceq
    #
    c0
    @0
    vn
    cv
    #
    @0
    chash
    cfv
    #
    cmo
    co
    #
    @3
    cop
    #
    csubstr
    co
    #
    @0
    cc0
    @4
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    cW
    c0
    wceq
    #
    c0
    cW
    cN
    cW
    chash
    cfv
    #
    cmo
    co
    #
    @11
    cop
    #
    csubstr
    co
    #
    cW
    cc0
    @12
    cop
    #
    csubstr
    co
    #
    cconcat
    co
    #
    cif
    ccsh
    @0
    cW
    wceq
    #
    @2
    cN
    wceq
    #
    wa
    #
    @1
    @10
    @9
    @17
    c0
    @18
    @1
    @10
    wb
    @19
    @0
    cW
    c0
    eqeq1
    adantr
    @20
    @6
    @14
    @8
    @16
    cconcat
    @20
    @0
    cW
    @5
    @13
    csubstr
    @18
    @19
    simpl
    #
    @20
    @4
    @12
    @3
    @11
    @20
    @2
    cN
    @3
    @11
    cmo
    @18
    @19
    simpr
    @18
    @3
    @11
    wceq
    @19
    @0
    cW
    chash
    fveq2
    adantr
    #
    oveq12d
    #
    @22
    opeq12d
    oveq12d
    @20
    @0
    cW
    @7
    @15
    csubstr
    @21
    @20
    @4
    @12
    cc0
    @23
    opeq2d
    oveq12d
    oveq12d
    ifbieq2d
    vw
    vf
    vn
    vl
    df-csh
    @10
    c0
    @17
    0ex
    @14
    @16
    cconcat
    ovex
    ifex
    ovmpt2a
end
