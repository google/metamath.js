include "cn.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "copab.mm"
include "cdom.mm"
include "cen.mm"
include "cxp.mm"
include "cvv.mm"
include "wss.mm"
include "nnex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssdomg.mm"
include "mp2.mm"
include "xpnnen.mm"
include "domentr.mm"
include "mp2an.mm"
include "cdenom.mm"
include "cneg.mm"
include "crab.mm"
include "crp.mm"
include "cdif.mm"
include "nnrp.mm"
include "rpsqrtcld.mm"
include "anim1i.mm"
include "eldif.mm"
include "sylibr.mm"
include "irrapx1.mm"
include "ensym.mm"
include "3syl.mm"
include "pellexlem3.mm"
include "endomtr.mm"
include "syl2anc.mm"
include "sbth.mm"
include "sylancr.mm"

theorem pellexlem4
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let vx: setvar x
  let wph: wff ph

  disjoint D y
  disjoint D z
  disjoint y z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint A e
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint g x
  disjoint a y
  disjoint b y
  disjoint c y
  disjoint d y
  disjoint e y
  disjoint f y
  disjoint g y
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint g z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint g ph
  assert |- ( ( D e. NN /\ -. ( sqrt ` D ) e. QQ ) -> { <. y , z >. | ( ( y e. NN /\ z e. NN ) /\ ( ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) =/= 0 /\ ( abs ` ( ( y ^ 2 ) - ( D x. ( z ^ 2 ) ) ) ) < ( 1 + ( 2 x. ( sqrt ` D ) ) ) ) ) } ~~ NN )

  proof
    cD
    cn
    wcel
    #
    cD
    csqrt
    cfv
    #
    cq
    wcel
    wn
    #
    wa
    #
    vy
    cv
    #
    cn
    wcel
    vz
    cv
    #
    cn
    wcel
    wa
    @4
    c2
    cexp
    co
    cD
    @5
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    #
    cc0
    wne
    @6
    cabs
    cfv
    c1
    c2
    @1
    cmul
    co
    caddc
    co
    clt
    wbr
    wa
    #
    wa
    vy
    vz
    copab
    #
    cn
    cdom
    wbr
    #
    cn
    @8
    cdom
    wbr
    #
    @8
    cn
    cen
    wbr
    @8
    cn
    cn
    cxp
    #
    cdom
    wbr
    #
    @11
    cn
    cen
    wbr
    @9
    @11
    cvv
    wcel
    @8
    @11
    wss
    @12
    cn
    cn
    nnex
    nnex
    xpex
    @7
    vy
    vz
    cn
    cn
    opabssxp
    @8
    @11
    cvv
    ssdomg
    mp2
    xpnnen
    @8
    @11
    cn
    domentr
    mp2an
    @3
    cn
    cc0
    vb
    cv
    #
    clt
    wbr
    @13
    @1
    cmin
    co
    cabs
    cfv
    @13
    cdenom
    cfv
    c2
    cneg
    cexp
    co
    clt
    wbr
    wa
    vb
    cq
    crab
    #
    cen
    wbr
    #
    @14
    @8
    cdom
    wbr
    @10
    @3
    @1
    crp
    cq
    cdif
    wcel
    #
    @14
    cn
    cen
    wbr
    @15
    @3
    @1
    crp
    wcel
    #
    @2
    wa
    @16
    @0
    @17
    @2
    @0
    cD
    cD
    nnrp
    rpsqrtcld
    anim1i
    @1
    crp
    cq
    eldif
    sylibr
    vb
    @1
    irrapx1
    @14
    cn
    ensym
    3syl
    vb
    vy
    vz
    cD
    pellexlem3
    cn
    @14
    @8
    endomtr
    syl2anc
    @8
    cn
    sbth
    sylancr
end
