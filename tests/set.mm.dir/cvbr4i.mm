include "ccv.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cat.mm"
include "wrex.mm"
include "wa.mm"
include "cch.mm"
include "wcel.mm"
include "wi.mm"
include "cvpss.mm"
include "mp2an.mm"
include "cvati.mm"
include "jca.mm"
include "wb.mm"
include "chcv2.mm"
include "mpan.mm"
include "adantr.mm"
include "psseq2.mm"
include "adantl.mm"
include "breq2.mm"
include "3bitr3d.mm"
include "biimpd.mm"
include "ex.mm"
include "com3r.mm"
include "rexlimdv.mm"
include "imp.mm"
include "impbii.mm"

theorem cvbr4i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chpssat.1: |- A e. CH
  assume chpssat.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A <oH B <-> ( A C. B /\ E. x e. HAtoms ( A vH x ) = B ) )

  proof
    cA
    cB
    ccv
    wbr
    #
    cA
    cB
    wpss
    #
    cA
    vx
    cv
    #
    chj
    co
    #
    cB
    wceq
    #
    vx
    cat
    wrex
    #
    wa
    @0
    @1
    @5
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    @0
    @1
    wi
    chpssat.1
    chpssat.2
    cA
    cB
    cvpss
    mp2an
    vx
    cA
    cB
    chpssat.1
    chpssat.2
    cvati
    jca
    @1
    @5
    @0
    @1
    @4
    @0
    vx
    cat
    @2
    cat
    wcel
    #
    @4
    @1
    @0
    @7
    @4
    @1
    @0
    wi
    @7
    @4
    wa
    #
    @1
    @0
    @8
    cA
    @3
    wpss
    #
    cA
    @3
    ccv
    wbr
    #
    @1
    @0
    @7
    @9
    @10
    wb
    #
    @4
    @6
    @7
    @11
    chpssat.1
    cA
    @2
    chcv2
    mpan
    adantr
    @4
    @9
    @1
    wb
    @7
    @3
    cB
    cA
    psseq2
    adantl
    @4
    @10
    @0
    wb
    @7
    @3
    cB
    cA
    ccv
    breq2
    adantl
    3bitr3d
    biimpd
    ex
    com3r
    rexlimdv
    imp
    impbii
end
