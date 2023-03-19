include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cr.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "csu.mm"
include "eqid.mm"
include "cxmt.mm"
include "ctopon.mm"
include "cme.mm"
include "metxmet.mm"
include "syl.mm"
include "mopntopon.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "adantr.mm"
include "difssd.mm"
include "sselda.mm"
include "toponss.mm"
include "syl2anc.mm"
include "wn.mm"
include "wceq.mm"
include "eleq1.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "pssdifn0.mm"
include "metdscn2.mm"
include "syl3anc.mm"
include "fsumcn.mm"
include "syl5eqel.mm"
include "cc.mm"
include "wb.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "crp.mm"
include "wf.mm"
include "lebnumlem1.mm"
include "frn.mm"
include "rpssre.mm"
include "syl6ss.mm"
include "ax-resscn.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "cioo.mm"
include "ctg.mm"
include "tgioo2.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"

theorem lebnumlem2
  let wph: wff ph
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vd: setvar d
  let vm: setvar m
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  assume lebnum.j: |- J = ( MetOpen ` D )
  assume lebnum.d: |- ( ph -> D e. ( Met ` X ) )
  assume lebnum.c: |- ( ph -> J e. Comp )
  assume lebnum.s: |- ( ph -> U C_ J )
  assume lebnum.u: |- ( ph -> X = U. U )
  assume lebnumlem1.u: |- ( ph -> U e. Fin )
  assume lebnumlem1.n: |- ( ph -> -. X e. U )
  assume lebnumlem1.f: |- F = ( y e. X |-> sum_ k e. U inf ( ran ( z e. ( X \ k ) |-> ( y D z ) ) , RR* , < ) )
  assume lebnumlem2.k: |- K = ( topGen ` ran (,) )

  disjoint k y
  disjoint k z
  disjoint D k
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint J k
  disjoint J y
  disjoint J z
  disjoint U k
  disjoint U y
  disjoint U z
  disjoint k ph
  disjoint ph y
  disjoint ph z
  disjoint X k
  disjoint X y
  disjoint X z
  disjoint d k
  disjoint d m
  disjoint d r
  disjoint d u
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint k m
  disjoint k r
  disjoint k u
  disjoint k w
  disjoint k x
  disjoint m r
  disjoint m u
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint D r
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint D u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint J d
  disjoint J w
  disjoint J x
  disjoint U d
  disjoint U m
  disjoint U r
  disjoint U u
  disjoint U w
  disjoint U x
  disjoint F r
  disjoint F w
  disjoint F x
  disjoint d ph
  disjoint m ph
  disjoint ph r
  disjoint ph w
  disjoint ph x
  disjoint X d
  disjoint X m
  disjoint X r
  disjoint X u
  disjoint X w
  disjoint X x
  disjoint K x
  assert |- ( ph -> F e. ( J Cn K ) )

  proof
    wph
    cF
    cJ
    ccnfld
    ctopn
    cfv
    #
    cr
    crest
    co
    #
    ccn
    co
    #
    cJ
    cK
    ccn
    co
    wph
    cF
    cJ
    @0
    ccn
    co
    #
    wcel
    #
    cF
    @2
    wcel
    #
    wph
    cF
    vy
    cX
    cU
    vz
    cX
    vk
    cv
    #
    cdif
    #
    vy
    cv
    vz
    cv
    cD
    co
    cmpt
    crn
    cxr
    clt
    cinf
    #
    vk
    csu
    cmpt
    @3
    lebnumlem1.f
    wph
    vy
    cU
    @8
    vk
    cJ
    @0
    cX
    @0
    eqid
    #
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @10
    lebnum.d
    cD
    cX
    metxmet
    syl
    #
    cD
    cJ
    cX
    lebnum.j
    mopntopon
    #
    syl
    lebnumlem1.u
    wph
    @6
    cU
    wcel
    #
    wa
    #
    @12
    @7
    cX
    wss
    @7
    c0
    wne
    #
    vy
    cX
    @8
    cmpt
    #
    @3
    wcel
    wph
    @12
    @15
    lebnum.d
    adantr
    @16
    cX
    @6
    difssd
    @16
    @6
    cX
    wss
    #
    @6
    cX
    wne
    #
    @17
    @16
    @11
    @6
    cJ
    wcel
    @19
    @16
    @10
    @11
    wph
    @10
    @15
    @13
    adantr
    @14
    syl
    wph
    cU
    cJ
    @6
    lebnum.s
    sselda
    @6
    cJ
    cX
    toponss
    syl2anc
    wph
    @15
    @20
    wph
    @15
    @6
    cX
    wph
    @15
    wn
    @6
    cX
    wceq
    #
    cX
    cU
    wcel
    #
    wn
    lebnumlem1.n
    @21
    @15
    @22
    @6
    cX
    cU
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    imp
    @6
    cX
    pssdifn0
    syl2anc
    vy
    vz
    cD
    @7
    @18
    cJ
    @0
    cX
    @18
    eqid
    lebnum.j
    @9
    metdscn2
    syl3anc
    fsumcn
    syl5eqel
    wph
    @0
    cc
    ctopon
    cfv
    wcel
    #
    cF
    crn
    #
    cr
    wss
    cr
    cc
    wss
    #
    @4
    @5
    wb
    @23
    wph
    @0
    @9
    cnfldtopon
    a1i
    wph
    @24
    crp
    cr
    wph
    cX
    crp
    cF
    wf
    @24
    crp
    wss
    wph
    vy
    vz
    cD
    cU
    vk
    cF
    cJ
    cX
    lebnum.j
    lebnum.d
    lebnum.c
    lebnum.s
    lebnum.u
    lebnumlem1.u
    lebnumlem1.n
    lebnumlem1.f
    lebnumlem1
    cX
    crp
    cF
    frn
    syl
    rpssre
    syl6ss
    @25
    wph
    ax-resscn
    a1i
    cr
    cF
    cJ
    @0
    cc
    cnrest2
    syl3anc
    mpbid
    cK
    @1
    cJ
    ccn
    cK
    cioo
    crn
    ctg
    cfv
    @1
    lebnumlem2.k
    @0
    @9
    tgioo2
    eqtri
    oveq2i
    syl6eleqr
end
