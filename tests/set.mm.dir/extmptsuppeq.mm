include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "csupp.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "cv.mm"
include "wss.mm"
include "adantl.mm"
include "sseld.mm"
include "anim1d.mm"
include "wn.mm"
include "eldif.mm"
include "adantll.mm"
include "sylan2br.mm"
include "expr.mm"
include "elsn2g.mm"
include "elndif.mm"
include "syl6bir.mm"
include "ad2antrr.mm"
include "syld.mm"
include "con4d.mm"
include "impr.mm"
include "simprr.mm"
include "jca.mm"
include "ex.mm"
include "impbid.mm"
include "rabbidva2.mm"
include "eqid.mm"
include "ssexd.mm"
include "simpl.mm"
include "mptsuppdifd.mm"
include "3eqtr4d.mm"
include "c0.mm"
include "simpr.mm"
include "con3i.mm"
include "supp0prc.mm"
include "syl.mm"
include "eqtr4d.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem extmptsuppeq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cW: class W
  let cX: class X
  let cZ: class Z
  assume extmptsuppeq.b: |- ( ph -> B e. W )
  assume extmptsuppeq.a: |- ( ph -> A C_ B )
  assume extmptsuppeq.z: |- ( ( ph /\ n e. ( B \ A ) ) -> X = Z )

  disjoint A n
  disjoint B n
  disjoint Z n
  disjoint n ph
  assert |- ( ph -> ( ( n e. A |-> X ) supp Z ) = ( ( n e. B |-> X ) supp Z ) )

  proof
    cZ
    cvv
    wcel
    #
    wph
    vn
    cA
    cX
    cmpt
    #
    cZ
    csupp
    co
    #
    vn
    cB
    cX
    cmpt
    #
    cZ
    csupp
    co
    #
    wceq
    #
    wi
    @0
    wph
    @5
    @0
    wph
    wa
    #
    cX
    cvv
    cZ
    csn
    #
    cdif
    wcel
    #
    vn
    cA
    crab
    @8
    vn
    cB
    crab
    @2
    @4
    @6
    @8
    @8
    vn
    cA
    cB
    @6
    vn
    cv
    #
    cA
    wcel
    #
    @8
    wa
    #
    @9
    cB
    wcel
    #
    @8
    wa
    #
    @6
    @10
    @12
    @8
    @6
    cA
    cB
    @9
    wph
    cA
    cB
    wss
    @0
    extmptsuppeq.a
    adantl
    sseld
    anim1d
    @6
    @13
    @11
    @6
    @13
    wa
    @10
    @8
    @6
    @12
    @8
    @10
    @6
    @12
    wa
    #
    @10
    @8
    @14
    @10
    wn
    #
    cX
    cZ
    wceq
    #
    @8
    wn
    #
    @6
    @12
    @15
    @16
    @12
    @15
    wa
    @6
    @9
    cB
    cA
    cdif
    wcel
    #
    @16
    @9
    cB
    cA
    eldif
    wph
    @18
    @16
    @0
    extmptsuppeq.z
    adantll
    sylan2br
    expr
    @0
    @16
    @17
    wi
    wph
    @12
    @0
    @16
    cX
    @7
    wcel
    @17
    cX
    cZ
    cvv
    elsn2g
    cX
    @7
    cvv
    elndif
    syl6bir
    ad2antrr
    syld
    con4d
    impr
    @6
    @12
    @8
    simprr
    jca
    ex
    impbid
    rabbidva2
    @6
    vn
    cA
    cX
    @1
    cvv
    cvv
    cZ
    @1
    eqid
    wph
    cA
    cvv
    wcel
    @0
    wph
    cA
    cB
    cW
    extmptsuppeq.b
    extmptsuppeq.a
    ssexd
    adantl
    @0
    wph
    simpl
    #
    mptsuppdifd
    @6
    vn
    cB
    cX
    @3
    cW
    cvv
    cZ
    @3
    eqid
    wph
    cB
    cW
    wcel
    @0
    extmptsuppeq.b
    adantl
    @19
    mptsuppdifd
    3eqtr4d
    ex
    @0
    wn
    #
    @5
    wph
    @20
    @2
    c0
    @4
    @20
    @1
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    @2
    c0
    wceq
    @22
    @0
    @21
    @0
    simpr
    con3i
    @1
    cZ
    supp0prc
    syl
    @20
    @3
    cvv
    wcel
    #
    @0
    wa
    #
    wn
    @4
    c0
    wceq
    @24
    @0
    @23
    @0
    simpr
    con3i
    @3
    cZ
    supp0prc
    syl
    eqtr4d
    a1d
    pm2.61i
end
