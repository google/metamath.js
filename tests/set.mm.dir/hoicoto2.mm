include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "c2nd.mm"
include "cr.mm"
include "cxp.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "cvv.mm"
include "wceq.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "elexd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "xp2nd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "ixpeq2dva.mm"

theorem hoicoto2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume hoicoto2.i: |- ( ph -> I : X --> ( RR X. RR ) )
  assume hoicoto2.a: |- A = ( k e. X |-> ( 1st ` ( I ` k ) ) )
  assume hoicoto2.b: |- B = ( k e. X |-> ( 2nd ` ( I ` k ) ) )

  disjoint X k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> X_ k e. X ( ( [,) o. I ) ` k ) = X_ k e. X ( ( A ` k ) [,) ( B ` k ) ) )

  proof
    wph
    vk
    cX
    vk
    cv
    #
    cico
    cI
    ccom
    cfv
    #
    @0
    cA
    cfv
    #
    @0
    cB
    cfv
    #
    cico
    co
    #
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @1
    @0
    cI
    cfv
    #
    c1st
    cfv
    #
    @7
    c2nd
    cfv
    #
    cico
    co
    @4
    @6
    cI
    cico
    cr
    cr
    cX
    @0
    wph
    cX
    cr
    cr
    cxp
    #
    cI
    wf
    @5
    hoicoto2.i
    adantr
    wph
    @5
    simpr
    #
    fvovco
    @6
    @8
    @2
    @9
    @3
    cico
    @6
    @2
    @8
    @6
    @5
    @8
    cvv
    wcel
    @2
    @8
    wceq
    @11
    @6
    @8
    cr
    @6
    @7
    @10
    wcel
    #
    @8
    cr
    wcel
    wph
    cX
    @10
    @0
    cI
    hoicoto2.i
    ffvelrnda
    #
    @7
    cr
    cr
    xp1st
    syl
    elexd
    vk
    cX
    @8
    cvv
    cA
    hoicoto2.a
    fvmpt2
    syl2anc
    eqcomd
    @6
    @3
    @9
    @6
    @5
    @9
    cvv
    wcel
    @3
    @9
    wceq
    @11
    @6
    @9
    cr
    @6
    @12
    @9
    cr
    wcel
    @13
    @7
    cr
    cr
    xp2nd
    syl
    elexd
    vk
    cX
    @9
    cvv
    cB
    hoicoto2.b
    fvmpt2
    syl2anc
    eqcomd
    oveq12d
    eqtrd
    ixpeq2dva
end
