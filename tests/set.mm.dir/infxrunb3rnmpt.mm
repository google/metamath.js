include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cmnf.mm"
include "wceq.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfv.mm"
include "nfrex.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "simpr.mm"
include "eqid.mm"
include "elrnmpt1.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "simp3.mm"
include "breq1.mm"
include "rspcev.mm"
include "3exp.mm"
include "rexlimd.mm"
include "wi.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "biimpcd.mm"
include "a1d.mm"
include "reximdai.mm"
include "com12.mm"
include "syl.mm"
include "rexlimi.mm"
include "a1i.mm"
include "impbid.mm"
include "ralbid.mm"
include "wss.mm"
include "rnmptssd.mm"
include "infxrunb3.mm"
include "bitrd.mm"

theorem infxrunb3rnmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  assume infxrunb3rnmpt.1: |- F/ x ph
  assume infxrunb3rnmpt.2: |- F/ y ph
  assume infxrunb3rnmpt.3: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  assert |- ( ph -> ( A. y e. RR E. x e. A B <_ y <-> inf ( ran ( x e. A |-> B ) , RR* , < ) = -oo ) )

  proof
    wph
    cB
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wrex
    #
    vy
    cr
    wral
    vz
    cv
    #
    @0
    cle
    wbr
    #
    vz
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    wrex
    #
    vy
    cr
    wral
    #
    @6
    cxr
    clt
    cinf
    cmnf
    wceq
    #
    wph
    @2
    @7
    vy
    cr
    infxrunb3rnmpt.2
    wph
    @2
    @7
    wph
    @1
    @7
    vx
    cA
    infxrunb3rnmpt.1
    @4
    vx
    vz
    @6
    vx
    @5
    vx
    cA
    cB
    nfmpt1
    nfrn
    @4
    vx
    nfv
    #
    nfrex
    wph
    vx
    cv
    cA
    wcel
    #
    @1
    @7
    wph
    @11
    @1
    w3a
    cB
    @6
    wcel
    #
    @1
    @7
    wph
    @11
    @12
    @1
    wph
    @11
    wa
    @11
    cB
    cxr
    wcel
    @12
    wph
    @11
    simpr
    infxrunb3rnmpt.3
    vx
    cA
    cB
    @5
    cxr
    @5
    eqid
    #
    elrnmpt1
    syl2anc
    3adant3
    wph
    @11
    @1
    simp3
    @4
    @1
    vz
    cB
    @6
    @3
    cB
    @0
    cle
    breq1
    #
    rspcev
    syl2anc
    3exp
    rexlimd
    @7
    @2
    wi
    wph
    @4
    @2
    vz
    @6
    @2
    vz
    nfv
    @3
    @6
    wcel
    #
    @3
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @4
    @2
    wi
    @15
    @17
    @3
    cvv
    wcel
    @15
    @17
    wb
    vz
    vex
    vx
    cA
    cB
    @3
    @5
    cvv
    @13
    elrnmpt
    ax-mp
    biimpi
    @4
    @17
    @2
    @4
    @16
    @1
    vx
    cA
    @10
    @4
    @16
    @1
    wi
    @11
    @16
    @4
    @1
    @14
    biimpcd
    a1d
    reximdai
    com12
    syl
    rexlimi
    a1i
    impbid
    ralbid
    wph
    @6
    cxr
    wss
    @8
    @9
    wb
    wph
    vx
    cA
    cB
    cxr
    @5
    infxrunb3rnmpt.1
    @13
    infxrunb3rnmpt.3
    rnmptssd
    vy
    vz
    @6
    infxrunb3
    syl
    bitrd
end
