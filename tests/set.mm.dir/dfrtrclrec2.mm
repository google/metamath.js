include "crtrcl.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "cn0.mm"
include "wrex.mm"
include "wb.mm"
include "wi.mm"
include "cvv.mm"
include "ciun.mm"
include "cmpt.mm"
include "wceq.mm"
include "wcel.mm"
include "nn0ex.mm"
include "ovex.mm"
include "iunex.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "breq.mm"
include "cop.mm"
include "eliun.mm"
include "a1i.mm"
include "df-br.mm"
include "rexbii.mm"
include "3bitr4g.mm"
include "sylan9bb.mm"
include "mpancom.mm"
include "df-rtrclrec.mm"
include "fveq1.mm"
include "breqd.mm"
include "bibi1d.mm"
include "imbi2d.mm"
include "ax-mp.mm"
include "mpbir.mm"

theorem dfrtrclrec2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let vn: setvar n
  let vr: setvar r
  assume rtrclreclem.1: |- ( ph -> Rel R )
  assume rtrclreclem.2: |- ( ph -> R e. _V )

  disjoint R n
  disjoint A n
  disjoint B n
  disjoint R r
  disjoint n r
  assert |- ( ph -> ( A ( t*rec ` R ) B <-> E. n e. NN0 A ( R ^r n ) B ) )

  proof
    wph
    cA
    cB
    cR
    crtrcl
    cfv
    #
    wbr
    #
    cA
    cB
    cR
    vn
    cv
    #
    crelexp
    co
    #
    wbr
    #
    vn
    cn0
    wrex
    #
    wb
    #
    wi
    #
    wph
    cA
    cB
    cR
    vr
    cvv
    vn
    cn0
    vr
    cv
    #
    @2
    crelexp
    co
    #
    ciun
    #
    cmpt
    #
    cfv
    #
    wbr
    #
    @5
    wb
    #
    wi
    #
    @12
    vn
    cn0
    @3
    ciun
    #
    wceq
    #
    wph
    @14
    wph
    cR
    cvv
    wcel
    @16
    cvv
    wcel
    @17
    rtrclreclem.2
    vn
    cn0
    @3
    nn0ex
    cR
    @2
    crelexp
    ovex
    iunex
    vr
    cR
    @10
    @16
    cvv
    cvv
    @11
    @8
    cR
    wceq
    vn
    cn0
    @9
    @3
    @8
    cR
    @2
    crelexp
    oveq1
    iuneq2d
    @11
    eqid
    fvmptg
    sylancl
    @17
    @13
    cA
    cB
    @16
    wbr
    #
    wph
    @5
    cA
    cB
    @12
    @16
    breq
    wph
    cA
    cB
    cop
    #
    @16
    wcel
    #
    @19
    @3
    wcel
    #
    vn
    cn0
    wrex
    #
    @18
    @5
    @20
    @22
    wb
    wph
    vn
    @19
    cn0
    @3
    eliun
    a1i
    cA
    cB
    @16
    df-br
    @4
    @21
    vn
    cn0
    cA
    cB
    @3
    df-br
    rexbii
    3bitr4g
    sylan9bb
    mpancom
    crtrcl
    @11
    wceq
    #
    @7
    @15
    wb
    vn
    vr
    df-rtrclrec
    @23
    @6
    @14
    wph
    @23
    @1
    @13
    @5
    @23
    @0
    @12
    cA
    cB
    cR
    crtrcl
    @11
    fveq1
    breqd
    bibi1d
    imbi2d
    ax-mp
    mpbir
end
