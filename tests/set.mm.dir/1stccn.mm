include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "ccnp.mm"
include "cfv.mm"
include "wral.mm"
include "cn.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wa.mm"
include "ccom.mm"
include "wi.mm"
include "wal.mm"
include "ctopon.mm"
include "wb.mm"
include "cncnp.mm"
include "syl2anc.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "c1stc.mm"
include "adantr.mm"
include "simpr.mm"
include "1stccnp.mm"
include "ralbidva.mm"
include "ralcom4.mm"
include "impexp.mm"
include "ralbii.mm"
include "r19.21v.mm"
include "bitri.mm"
include "df-ral.mm"
include "lmcl.mm"
include "sylan.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "imbi1d.mm"
include "syl6rbb.mm"
include "albidv.mm"
include "syl5bb.mm"
include "imbi2d.mm"
include "3bitrd.mm"

theorem 1stccn
  let wph: wff ph
  let vx: setvar x
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let cP: class P
  assume 1stccnp.1: |- ( ph -> J e. 1stc )
  assume 1stccnp.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume 1stccnp.3: |- ( ph -> K e. ( TopOn ` Y ) )
  assume 1stccn.7: |- ( ph -> F : X --> Y )

  disjoint f x
  disjoint F f
  disjoint F x
  disjoint J f
  disjoint J x
  disjoint f ph
  disjoint ph x
  disjoint K f
  disjoint K x
  disjoint X f
  disjoint X x
  disjoint Y f
  disjoint Y x
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint F j
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint F k
  disjoint u v
  disjoint u x
  disjoint F u
  disjoint v x
  disjoint F v
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint K j
  disjoint K k
  disjoint K u
  disjoint K v
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint Y j
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint P f
  disjoint P j
  disjoint P k
  disjoint P u
  disjoint P v
  assert |- ( ph -> ( F e. ( J Cn K ) <-> A. f ( f : NN --> X -> A. x ( f ( ~~>t ` J ) x -> ( F o. f ) ( ~~>t ` K ) ( F ` x ) ) ) ) )

  proof
    wph
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
    cn
    cX
    vf
    cv
    #
    wf
    #
    @4
    @1
    cJ
    clm
    cfv
    wbr
    #
    wa
    cF
    @4
    ccom
    @1
    cF
    cfv
    cK
    clm
    cfv
    wbr
    #
    wi
    #
    vf
    wal
    #
    vx
    cX
    wral
    #
    @5
    @6
    @7
    wi
    #
    vx
    wal
    #
    wi
    #
    vf
    wal
    #
    wph
    @0
    cX
    cY
    cF
    wf
    #
    @3
    wa
    #
    @3
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @0
    @16
    wb
    1stccnp.2
    1stccnp.3
    vx
    cF
    cJ
    cK
    cX
    cY
    cncnp
    syl2anc
    wph
    @15
    @3
    1stccn.7
    biantrurd
    bitr4d
    wph
    @2
    @9
    vx
    cX
    wph
    @1
    cX
    wcel
    #
    wa
    #
    @2
    @15
    @9
    wa
    @9
    @20
    @1
    vf
    cF
    cJ
    cK
    cX
    cY
    wph
    cJ
    c1stc
    wcel
    @19
    1stccnp.1
    adantr
    wph
    @17
    @19
    1stccnp.2
    adantr
    wph
    @18
    @19
    1stccnp.3
    adantr
    wph
    @19
    simpr
    1stccnp
    @20
    @15
    @9
    wph
    @15
    @19
    1stccn.7
    adantr
    biantrurd
    bitr4d
    ralbidva
    @10
    @8
    vx
    cX
    wral
    #
    vf
    wal
    wph
    @14
    @8
    vx
    vf
    cX
    ralcom4
    wph
    @21
    @13
    vf
    @21
    @5
    @11
    vx
    cX
    wral
    #
    wi
    #
    wph
    @13
    @21
    @5
    @11
    wi
    #
    vx
    cX
    wral
    @23
    @8
    @24
    vx
    cX
    @5
    @6
    @7
    impexp
    ralbii
    @5
    @11
    vx
    cX
    r19.21v
    bitri
    wph
    @22
    @12
    @5
    @22
    @19
    @11
    wi
    #
    vx
    wal
    wph
    @12
    @11
    vx
    cX
    df-ral
    wph
    @25
    @11
    vx
    wph
    @11
    @19
    @6
    wa
    #
    @7
    wi
    @25
    wph
    @6
    @26
    @7
    wph
    @6
    @19
    wph
    @6
    @19
    wph
    @17
    @6
    @19
    1stccnp.2
    @1
    @4
    cJ
    cX
    lmcl
    sylan
    ex
    pm4.71rd
    imbi1d
    @19
    @6
    @7
    impexp
    syl6rbb
    albidv
    syl5bb
    imbi2d
    syl5bb
    albidv
    syl5bb
    3bitrd
end
