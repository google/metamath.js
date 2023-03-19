include "cof.mm"
include "co.mm"
include "wf.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cn0.mm"
include "cvv.mm"
include "cmnd.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "ccmn.mm"
include "cmnmnd.mm"
include "syl.mm"
include "mulgnn0cl.mm"
include "3expb.mm"
include "sylan.mm"
include "psrbagf.mm"
include "syl2anc.mm"
include "inidm.mm"
include "off.mm"
include "wfun.mm"
include "cc0.mm"
include "csupp.mm"
include "cfn.mm"
include "wss.mm"
include "ovexd.mm"
include "wfn.mm"
include "ffn.mm"
include "offn.mm"
include "fnfun.mm"
include "c0g.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "psrbagfsupp.mm"
include "fsuppimpd.mm"
include "ssid.mm"
include "wceq.mm"
include "mulg0.mm"
include "adantl.mm"
include "c0ex.mm"
include "suppssof1.mm"
include "suppssfifsupp.mm"
include "syl32anc.mm"
include "jca.mm"

theorem psrbagev1
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let c.x: class .x.
  let vh: setvar h
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume psrbagev1.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrbagev1.c: |- C = ( Base ` T )
  assume psrbagev1.x: |- .x. = ( .g ` T )
  assume psrbagev1.z: |- .0. = ( 0g ` T )
  assume psrbagev1.t: |- ( ph -> T e. CMnd )
  assume psrbagev1.b: |- ( ph -> B e. D )
  assume psrbagev1.g: |- ( ph -> G : I --> C )
  assume psrbagev1.i: |- ( ph -> I e. _V )

  disjoint B h
  disjoint I h
  disjoint ph y
  disjoint ph z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint G z
  disjoint .x. y
  disjoint .x. z
  disjoint .0. z
  assert |- ( ph -> ( ( B oF .x. G ) : I --> C /\ ( B oF .x. G ) finSupp .0. ) )

  proof
    wph
    cI
    cC
    cB
    cG
    c.x
    cof
    #
    co
    #
    wf
    @1
    c.0
    cfsupp
    wbr
    #
    wph
    vy
    vz
    cI
    cI
    cI
    c.x
    cn0
    cC
    cC
    cB
    cG
    cvv
    cvv
    wph
    cT
    cmnd
    wcel
    #
    vy
    cv
    #
    cn0
    wcel
    #
    vz
    cv
    #
    cC
    wcel
    #
    wa
    @4
    @6
    c.x
    co
    cC
    wcel
    #
    wph
    cT
    ccmn
    wcel
    @3
    psrbagev1.t
    cT
    cmnmnd
    syl
    @3
    @5
    @7
    @8
    cC
    c.x
    cT
    @4
    @6
    psrbagev1.c
    psrbagev1.x
    mulgnn0cl
    3expb
    sylan
    wph
    cI
    cvv
    wcel
    #
    cB
    cD
    wcel
    #
    cI
    cn0
    cB
    wf
    #
    psrbagev1.i
    psrbagev1.b
    cD
    vh
    cB
    cI
    cvv
    psrbagev1.d
    psrbagf
    syl2anc
    #
    psrbagev1.g
    psrbagev1.i
    psrbagev1.i
    cI
    inidm
    #
    off
    wph
    @1
    cvv
    wcel
    @1
    wfun
    #
    c.0
    cvv
    wcel
    #
    cB
    cc0
    csupp
    co
    #
    cfn
    wcel
    @1
    c.0
    csupp
    co
    @16
    wss
    @2
    wph
    cB
    cG
    @0
    ovexd
    wph
    @1
    cI
    wfn
    @14
    wph
    cI
    cI
    c.x
    cI
    cB
    cG
    cvv
    cvv
    wph
    @11
    cB
    cI
    wfn
    @12
    cI
    cn0
    cB
    ffn
    syl
    wph
    cI
    cC
    cG
    wf
    cG
    cI
    wfn
    psrbagev1.g
    cI
    cC
    cG
    ffn
    syl
    psrbagev1.i
    psrbagev1.i
    @13
    offn
    cI
    @1
    fnfun
    syl
    @15
    wph
    c.0
    cT
    c0g
    cfv
    cvv
    psrbagev1.z
    cT
    c0g
    fvex
    eqeltri
    a1i
    wph
    cB
    cc0
    wph
    @10
    @9
    cB
    cc0
    cfsupp
    wbr
    psrbagev1.b
    psrbagev1.i
    cD
    vh
    cI
    cvv
    cB
    psrbagev1.d
    psrbagfsupp
    syl2anc
    fsuppimpd
    wph
    vz
    cB
    cG
    cI
    cC
    cvv
    @16
    c.x
    cn0
    cvv
    cc0
    c.0
    @16
    @16
    wss
    wph
    @16
    ssid
    a1i
    @7
    cc0
    @6
    c.x
    co
    c.0
    wceq
    wph
    cC
    c.x
    cT
    @6
    c.0
    psrbagev1.c
    psrbagev1.z
    psrbagev1.x
    mulg0
    adantl
    @12
    psrbagev1.g
    psrbagev1.i
    cc0
    cvv
    wcel
    wph
    c0ex
    a1i
    suppssof1
    @16
    @1
    cvv
    cvv
    c.0
    suppssfifsupp
    syl32anc
    jca
end
