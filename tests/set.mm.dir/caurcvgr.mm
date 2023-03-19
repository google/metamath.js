include "clsp.mm"
include "cfv.mm"
include "crli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "crp.mm"
include "c3.mm"
include "c1.mm"
include "cmul.mm"
include "wa.mm"
include "1rp.mm"
include "a1i.mm"
include "caucvgrlem.mm"
include "simpl.mm"
include "rexlimivw.mm"
include "syl.mm"
include "recnd.mm"
include "cdiv.mm"
include "wss.mm"
include "adantr.mm"
include "wf.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "simpr.mm"
include "3re.mm"
include "3pos.mm"
include "elrpii.mm"
include "rpdivcl.mm"
include "sylancl.mm"
include "reximi.mm"
include "ssrexv.mm"
include "sylc.mm"
include "rpcn.mm"
include "adantl.mm"
include "3cn.mm"
include "cc0.mm"
include "wne.mm"
include "3ne0.mm"
include "divcan2d.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "ax-resscn.mm"
include "fss.mm"
include "eqidd.mm"
include "rlim.mm"
include "mpbir2and.mm"

theorem caurcvgr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  let cR: class R
  assume caurcvgr.1: |- ( ph -> A C_ RR )
  assume caurcvgr.2: |- ( ph -> F : A --> RR )
  assume caurcvgr.3: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume caurcvgr.4: |- ( ph -> A. x e. RR+ E. j e. A A. k e. A ( j <_ k -> ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) )

  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint j y
  disjoint k y
  disjoint m y
  disjoint F m
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F y
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint R j
  disjoint R k
  disjoint R m
  disjoint R n
  disjoint R x
  assert |- ( ph -> F ~~>r ( limsup ` F ) )

  proof
    wph
    cF
    cF
    clsp
    cfv
    #
    crli
    wbr
    @0
    cc
    wcel
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @2
    cF
    cfv
    #
    @0
    cmin
    co
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    vj
    cr
    wrex
    #
    vy
    crp
    wral
    wph
    @0
    wph
    @0
    cr
    wcel
    #
    @3
    @5
    c3
    c1
    cmul
    co
    clt
    wbr
    wi
    vk
    cA
    wral
    #
    wa
    #
    vj
    cA
    wrex
    @10
    wph
    vx
    cA
    c1
    vj
    vk
    cF
    caurcvgr.1
    caurcvgr.2
    caurcvgr.3
    caurcvgr.4
    c1
    crp
    wcel
    wph
    1rp
    a1i
    caucvgrlem
    @12
    @10
    vj
    cA
    @10
    @11
    simpl
    rexlimivw
    syl
    recnd
    wph
    @9
    vy
    crp
    wph
    @6
    crp
    wcel
    #
    wa
    #
    @3
    @5
    c3
    @6
    c3
    cdiv
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    #
    vj
    cr
    wrex
    #
    @9
    @14
    cA
    cr
    wss
    #
    @19
    vj
    cA
    wrex
    #
    @20
    wph
    @21
    @13
    caurcvgr.1
    adantr
    #
    @14
    @10
    @19
    wa
    #
    vj
    cA
    wrex
    @22
    @14
    vx
    cA
    @15
    vj
    vk
    cF
    @23
    wph
    cA
    cr
    cF
    wf
    #
    @13
    caurcvgr.2
    adantr
    wph
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    @13
    caurcvgr.3
    adantr
    wph
    @3
    @4
    @1
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    wi
    vk
    cA
    wral
    vj
    cA
    wrex
    vx
    crp
    wral
    @13
    caurcvgr.4
    adantr
    @14
    @13
    c3
    crp
    wcel
    @15
    crp
    wcel
    wph
    @13
    simpr
    c3
    3re
    3pos
    elrpii
    @6
    c3
    rpdivcl
    sylancl
    caucvgrlem
    @24
    @19
    vj
    cA
    @10
    @19
    simpr
    reximi
    syl
    @19
    vj
    cA
    cr
    ssrexv
    sylc
    @14
    @18
    @8
    vj
    vk
    cr
    cA
    @14
    @17
    @7
    @3
    @14
    @16
    @6
    @5
    clt
    @14
    @6
    c3
    @13
    @6
    cc
    wcel
    wph
    @6
    rpcn
    adantl
    c3
    cc
    wcel
    @14
    3cn
    a1i
    c3
    cc0
    wne
    @14
    3ne0
    a1i
    divcan2d
    breq2d
    imbi2d
    rexralbidv
    mpbid
    ralrimiva
    wph
    vy
    vj
    vk
    cA
    @4
    @0
    cF
    wph
    @25
    cr
    cc
    wss
    cA
    cc
    cF
    wf
    caurcvgr.2
    ax-resscn
    cA
    cr
    cc
    cF
    fss
    sylancl
    caurcvgr.1
    wph
    @2
    cA
    wcel
    wa
    @4
    eqidd
    rlim
    mpbir2and
end
