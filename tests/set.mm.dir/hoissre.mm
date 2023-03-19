include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cico.mm"
include "ccom.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "co.mm"
include "cr.mm"
include "cxp.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "fvovco.mm"
include "cxr.mm"
include "wss.mm"
include "ffvelrnda.mm"
include "xp1st.mm"
include "syl.mm"
include "xp2nd.mm"
include "rexrd.mm"
include "icossre.mm"
include "syl2anc.mm"
include "eqsstrd.mm"

theorem hoissre
  let wph: wff ph
  let vk: setvar k
  let cI: class I
  let cX: class X
  let vx: setvar x
  assume hoissre.1: |- ( ph -> I : X --> ( RR X. RR ) )

  disjoint X k
  disjoint k x
  assert |- ( ( ph /\ k e. X ) -> ( ( [,) o. I ) ` k ) C_ RR )

  proof
    wph
    vk
    cv
    #
    cX
    wcel
    #
    wa
    #
    @0
    cico
    cI
    ccom
    cfv
    @0
    cI
    cfv
    #
    c1st
    cfv
    #
    @3
    c2nd
    cfv
    #
    cico
    co
    #
    cr
    @2
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
    @1
    hoissre.1
    adantr
    wph
    @1
    simpr
    fvovco
    @2
    @4
    cr
    wcel
    #
    @5
    cxr
    wcel
    @6
    cr
    wss
    @2
    @3
    @7
    wcel
    #
    @8
    wph
    cX
    @7
    @0
    cI
    hoissre.1
    ffvelrnda
    #
    @3
    cr
    cr
    xp1st
    syl
    @2
    @5
    @2
    @9
    @5
    cr
    wcel
    @10
    @3
    cr
    cr
    xp2nd
    syl
    rexrd
    @4
    @5
    icossre
    syl2anc
    eqsstrd
end
