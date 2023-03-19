include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cestrc.mm"
include "cfv.mm"
include "chom.mm"
include "cresc.mm"
include "cbs.mm"
include "csubc.mm"
include "wcel.mm"
include "wi.mm"
include "eqid.mm"
include "crng.mm"
include "cin.mm"
include "rngcbas.mm"
include "incom.mm"
include "syl6eq.mm"
include "rngchomfval.mm"
include "rnghmsubcsetc.mm"
include "idi.mm"
include "cid.mm"
include "cres.mm"
include "rngcval.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "eqtrd.mm"
include "cv.mm"
include "crngh.mm"
include "cmpt2.mm"
include "wceq.mm"
include "adantr.mm"
include "wa.mm"
include "cxp.mm"
include "oveqdr.mm"
include "ovres.mm"
include "adantl.mm"
include "eqtr2d.mm"
include "mpt2eq123dva.mm"
include "inclfusubc.mm"
include "a1i.mm"
include "oveq12d.mm"
include "breqd.mm"
include "mpbird.mm"

theorem rngcifuestrc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume rngcifuestrc.r: |- R = ( RngCat ` U )
  assume rngcifuestrc.e: |- E = ( ExtStrCat ` U )
  assume rngcifuestrc.b: |- B = ( Base ` R )
  assume rngcifuestrc.u: |- ( ph -> U e. V )
  assume rngcifuestrc.f: |- ( ph -> F = ( _I |` B ) )
  assume rngcifuestrc.g: |- ( ph -> G = ( x e. B , y e. B |-> ( _I |` ( x RngHomo y ) ) ) )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint U x
  disjoint U y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> F ( R Func E ) G )

  proof
    wph
    cF
    cG
    cR
    cE
    cfunc
    co
    #
    wbr
    cF
    cG
    cU
    cestrc
    cfv
    #
    cR
    chom
    cfv
    #
    cresc
    co
    #
    @1
    cfunc
    co
    #
    wbr
    wph
    vx
    vy
    @3
    cbs
    cfv
    #
    @1
    @3
    cF
    cG
    @2
    wph
    @2
    @1
    csubc
    cfv
    wcel
    wi
    wph
    cB
    @1
    cU
    @2
    cV
    @1
    eqid
    rngcifuestrc.u
    wph
    cB
    cU
    crng
    cin
    crng
    cU
    cin
    wph
    cB
    cR
    cU
    cV
    rngcifuestrc.r
    rngcifuestrc.b
    rngcifuestrc.u
    rngcbas
    #
    cU
    crng
    incom
    syl6eq
    wph
    cB
    cR
    cU
    @2
    cV
    rngcifuestrc.r
    rngcifuestrc.b
    rngcifuestrc.u
    @2
    eqid
    rngchomfval
    #
    rnghmsubcsetc
    idi
    @3
    eqid
    @5
    eqid
    wph
    cF
    cid
    cB
    cres
    cid
    @5
    cres
    rngcifuestrc.f
    wph
    cB
    @5
    cid
    wph
    cB
    cR
    cbs
    cfv
    @5
    rngcifuestrc.b
    wph
    cR
    @3
    cbs
    wph
    cB
    cR
    cU
    @2
    cV
    rngcifuestrc.r
    rngcifuestrc.u
    @6
    @7
    rngcval
    #
    fveq2d
    syl5eq
    #
    reseq2d
    eqtrd
    wph
    cG
    vx
    vy
    cB
    cB
    cid
    vx
    cv
    #
    vy
    cv
    #
    crngh
    co
    #
    cres
    #
    cmpt2
    vx
    vy
    @5
    @5
    cid
    @10
    @11
    @2
    co
    #
    cres
    #
    cmpt2
    rngcifuestrc.g
    wph
    vx
    vy
    cB
    cB
    @13
    @5
    @5
    @15
    @9
    wph
    cB
    @5
    wceq
    @10
    cB
    wcel
    #
    @9
    adantr
    wph
    @16
    @11
    cB
    wcel
    wa
    #
    wa
    #
    @12
    @14
    cid
    @18
    @14
    @10
    @11
    crngh
    cB
    cB
    cxp
    cres
    #
    co
    #
    @12
    wph
    @17
    vx
    vy
    @2
    @19
    @7
    oveqdr
    @17
    @20
    @12
    wceq
    wph
    @10
    @11
    cB
    cB
    crngh
    ovres
    adantl
    eqtr2d
    reseq2d
    mpt2eq123dva
    eqtrd
    inclfusubc
    wph
    @0
    @4
    cF
    cG
    wph
    cR
    @3
    cE
    @1
    cfunc
    @8
    cE
    @1
    wceq
    wph
    rngcifuestrc.e
    a1i
    oveq12d
    breqd
    mpbird
end
