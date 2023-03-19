include "climc.mm"
include "co.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "limccl.mm"
include "sseli.mm"
include "adantl.mm"
include "wa.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "c0.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "simpr.mm"
include "c1.mm"
include "1rp.mm"
include "ral0.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "rgenw.mm"
include "a1i.mm"
include "wf.mm"
include "adantr.mm"
include "wss.mm"
include "0ss.mm"
include "ellimc3.mm"
include "mpbir2and.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem limcdm0
  let wph: wff ph
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume limcdm0.f: |- ( ph -> F : (/) --> CC )
  assume limcdm0.b: |- ( ph -> B e. CC )


  assert |- ( ph -> ( F limCC B ) = CC )

  proof
    wph
    vx
    cF
    cB
    climc
    co
    #
    cc
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @1
    cc
    wcel
    #
    @2
    @3
    wph
    @0
    cc
    @1
    cB
    cF
    limccl
    sseli
    adantl
    wph
    @3
    wa
    #
    @2
    @3
    vz
    cv
    #
    cB
    wne
    #
    @5
    cB
    cmin
    co
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wa
    #
    @5
    cF
    cfv
    @1
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    #
    wi
    #
    vz
    c0
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    #
    wph
    @3
    simpr
    @15
    @4
    @14
    vy
    crp
    c1
    crp
    wcel
    @6
    @7
    c1
    clt
    wbr
    #
    wa
    #
    @11
    wi
    #
    vz
    c0
    wral
    #
    @14
    1rp
    @18
    vz
    ral0
    @13
    @19
    vw
    c1
    crp
    @8
    c1
    wceq
    #
    @12
    @18
    vz
    c0
    @20
    @10
    @17
    @11
    @20
    @9
    @16
    @6
    @8
    c1
    @7
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    mp2an
    rgenw
    a1i
    @4
    vy
    vw
    vz
    c0
    cB
    @1
    cF
    wph
    c0
    cc
    cF
    wf
    @3
    limcdm0.f
    adantr
    c0
    cc
    wss
    @4
    cc
    0ss
    a1i
    wph
    cB
    cc
    wcel
    @3
    limcdm0.b
    adantr
    ellimc3
    mpbir2and
    impbida
    eqrdv
end
