include "cv.mm"
include "cpw.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "w3a.mm"
include "c0.mm"
include "wceq.mm"
include "cuni.mm"
include "wa.mm"
include "unieq.mm"
include "uni0.mm"
include "a1i.mm"
include "eqtrd.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "3ad2antl1.mm"
include "wn.mm"
include "wne.mm"
include "neqne.mm"
include "cn.mm"
include "wfo.mm"
include "wex.mm"
include "nnfoctb.mm"
include "3ad2antl3.mm"
include "wi.mm"
include "cfv.mm"
include "ciun.mm"
include "founiiun.mm"
include "wf.mm"
include "simpll.mm"
include "fof.mm"
include "wss.mm"
include "elpwi.mm"
include "fssd.mm"
include "adantll.mm"
include "syl2anc.mm"
include "ex.mm"
include "3adantl3.mm"
include "exlimdv.mm"
include "mpd.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "issald.mm"

theorem issalnnd
  let wph: wff ph
  let vy: setvar y
  let cS: class S
  let ve: setvar e
  let vn: setvar n
  let cV: class V
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume issalnnd.s: |- ( ph -> S e. V )
  assume issalnnd.z: |- ( ph -> (/) e. S )
  assume issalnnd.x: |- X = U. S
  assume issalnnd.d: |- ( ( ph /\ y e. S ) -> ( X \ y ) e. S )
  assume issalnnd.i: |- ( ( ph /\ e : NN --> S ) -> U_ n e. NN ( e ` n ) e. S )

  disjoint S e
  disjoint S y
  disjoint e y
  disjoint e n
  disjoint n y
  disjoint e ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> S e. SAlg )

  proof
    wph
    vy
    cS
    cV
    cX
    issalnnd.s
    issalnnd.z
    issalnnd.x
    issalnnd.d
    wph
    vy
    cv
    #
    cS
    cpw
    wcel
    #
    @0
    com
    cdom
    wbr
    #
    w3a
    #
    @0
    c0
    wceq
    #
    @0
    cuni
    #
    cS
    wcel
    #
    wph
    @1
    @4
    @6
    @2
    wph
    @4
    wa
    @5
    c0
    cS
    @4
    @5
    c0
    wceq
    wph
    @4
    @5
    c0
    cuni
    #
    c0
    @0
    c0
    unieq
    @7
    c0
    wceq
    @4
    uni0
    a1i
    eqtrd
    adantl
    wph
    c0
    cS
    wcel
    @4
    issalnnd.z
    adantr
    eqeltrd
    3ad2antl1
    @3
    @4
    wn
    #
    @0
    c0
    wne
    #
    @6
    @8
    @9
    @3
    @0
    c0
    neqne
    adantl
    @3
    @9
    wa
    #
    cn
    @0
    ve
    cv
    #
    wfo
    #
    ve
    wex
    #
    @6
    @2
    wph
    @9
    @13
    @1
    @0
    ve
    nnfoctb
    3ad2antl3
    @10
    @12
    @6
    ve
    wph
    @1
    @9
    @12
    @6
    wi
    #
    @2
    wph
    @1
    wa
    #
    @14
    @9
    @15
    @12
    @6
    @15
    @12
    wa
    #
    @5
    vn
    cn
    vn
    cv
    @11
    cfv
    ciun
    #
    cS
    @12
    @5
    @17
    wceq
    @15
    vn
    cn
    @0
    @11
    founiiun
    adantl
    @16
    wph
    cn
    cS
    @11
    wf
    #
    @17
    cS
    wcel
    wph
    @1
    @12
    simpll
    @1
    @12
    @18
    wph
    @1
    @12
    wa
    cn
    @0
    cS
    @11
    @12
    cn
    @0
    @11
    wf
    @1
    cn
    @0
    @11
    fof
    adantl
    @1
    @0
    cS
    wss
    @12
    @0
    cS
    elpwi
    adantr
    fssd
    adantll
    issalnnd.i
    syl2anc
    eqeltrd
    ex
    adantr
    3adantl3
    exlimdv
    mpd
    syldan
    pm2.61dan
    issald
end
