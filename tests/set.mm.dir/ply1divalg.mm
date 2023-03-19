include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "cmulr.mm"
include "cur.mm"
include "cco1.mm"
include "cinvr.mm"
include "cbs.mm"
include "eqid.mm"
include "crg.mm"
include "wcel.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "wceq.mm"
include "unitrinv.mm"
include "ply1divex.mm"
include "crlreg.mm"
include "wss.mm"
include "unitrrg.mm"
include "syl.mm"
include "sseldd.mm"
include "ply1divmo.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem ply1divalg
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let c.xb: class .xb
  let cU: class U
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let c.0: class .0.
  let vq: setvar q
  assume ply1divalg.p: |- P = ( Poly1 ` R )
  assume ply1divalg.d: |- D = ( deg1 ` R )
  assume ply1divalg.b: |- B = ( Base ` P )
  assume ply1divalg.m: |- .- = ( -g ` P )
  assume ply1divalg.z: |- .0. = ( 0g ` P )
  assume ply1divalg.t: |- .xb = ( .r ` P )
  assume ply1divalg.r1: |- ( ph -> R e. Ring )
  assume ply1divalg.f: |- ( ph -> F e. B )
  assume ply1divalg.g1: |- ( ph -> G e. B )
  assume ply1divalg.g2: |- ( ph -> G =/= .0. )
  assume ply1divalg.g3: |- ( ph -> ( ( coe1 ` G ) ` ( D ` G ) ) e. U )
  assume ply1divalg.u: |- U = ( Unit ` R )

  disjoint ph q
  disjoint B q
  disjoint D q
  disjoint F q
  disjoint G q
  disjoint .- q
  disjoint P q
  disjoint R q
  disjoint .xb q
  disjoint .0. q
  assert |- ( ph -> E! q e. B ( D ` ( F .- ( G .xb q ) ) ) < ( D ` G ) )

  proof
    wph
    cF
    cG
    vq
    cv
    c.xb
    co
    c.mi
    co
    cD
    cfv
    cG
    cD
    cfv
    #
    clt
    wbr
    #
    vq
    cB
    wrex
    @1
    vq
    cB
    wrmo
    @1
    vq
    cB
    wreu
    wph
    cB
    cD
    cP
    cR
    c.xb
    cR
    cmulr
    cfv
    #
    cR
    cur
    cfv
    #
    cF
    cG
    @0
    cG
    cco1
    cfv
    cfv
    #
    cR
    cinvr
    cfv
    #
    cfv
    #
    cR
    cbs
    cfv
    #
    c.mi
    c.0
    vq
    ply1divalg.p
    ply1divalg.d
    ply1divalg.b
    ply1divalg.m
    ply1divalg.z
    ply1divalg.t
    ply1divalg.r1
    ply1divalg.f
    ply1divalg.g1
    ply1divalg.g2
    @3
    eqid
    #
    @7
    eqid
    #
    @2
    eqid
    #
    wph
    cR
    crg
    wcel
    #
    @4
    cU
    wcel
    #
    @6
    @7
    wcel
    ply1divalg.r1
    ply1divalg.g3
    @7
    cR
    cU
    @5
    @4
    ply1divalg.u
    @5
    eqid
    #
    @9
    ringinvcl
    syl2anc
    wph
    @11
    @12
    @4
    @6
    @2
    co
    @3
    wceq
    ply1divalg.r1
    ply1divalg.g3
    cR
    @2
    cU
    @3
    @5
    @4
    ply1divalg.u
    @13
    @10
    @8
    unitrinv
    syl2anc
    ply1divex
    wph
    cB
    cD
    cP
    cR
    c.xb
    cR
    crlreg
    cfv
    #
    cF
    cG
    c.mi
    c.0
    vq
    ply1divalg.p
    ply1divalg.d
    ply1divalg.b
    ply1divalg.m
    ply1divalg.z
    ply1divalg.t
    ply1divalg.r1
    ply1divalg.f
    ply1divalg.g1
    ply1divalg.g2
    wph
    cU
    @14
    @4
    wph
    @11
    cU
    @14
    wss
    ply1divalg.r1
    cR
    cU
    @14
    @14
    eqid
    #
    ply1divalg.u
    unitrrg
    syl
    ply1divalg.g3
    sseldd
    @15
    ply1divmo
    @1
    vq
    cB
    reu5
    sylanbrc
end
