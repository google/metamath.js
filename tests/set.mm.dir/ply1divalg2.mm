include "cv.mm"
include "co.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wreu.mm"
include "coppr.mm"
include "cpl1.mm"
include "cmulr.mm"
include "eqid.mm"
include "cdg1.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqidd.mm"
include "opprbas.mm"
include "a1i.mm"
include "cplusg.mm"
include "wcel.mm"
include "wa.mm"
include "oppradd.mm"
include "oveqi.mm"
include "deg1propd.mm"
include "trud.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "ply1baspropd.mm"
include "csg.mm"
include "ply1plusgpropd.mm"
include "grpsubpropd.mm"
include "c0g.mm"
include "grpidpropd.mm"
include "crg.mm"
include "opprring.mm"
include "syl.mm"
include "opprunit.mm"
include "ply1divalg.mm"
include "adantr.mm"
include "simpr.mm"
include "ply1opprmul.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "reubidva.mm"
include "mpbird.mm"

theorem ply1divalg2
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
  let vr: setvar r
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
  disjoint B r
  disjoint P r
  disjoint R r
  disjoint q r
  assert |- ( ph -> E! q e. B ( D ` ( F .- ( q .xb G ) ) ) < ( D ` G ) )

  proof
    wph
    cF
    vq
    cv
    #
    cG
    c.xb
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    clt
    wbr
    #
    vq
    cB
    wreu
    cF
    cG
    @0
    cR
    coppr
    cfv
    #
    cpl1
    cfv
    #
    cmulr
    cfv
    #
    co
    #
    c.mi
    co
    #
    cD
    cfv
    #
    @4
    clt
    wbr
    #
    vq
    cB
    wreu
    wph
    cB
    cD
    @7
    @6
    @8
    cU
    cF
    cG
    c.mi
    c.0
    vq
    @7
    eqid
    #
    cD
    cR
    cdg1
    cfv
    #
    @6
    cdg1
    cfv
    #
    ply1divalg.d
    @14
    @15
    wceq
    wtru
    vq
    vr
    cR
    cbs
    cfv
    #
    cR
    @6
    wtru
    @16
    eqidd
    #
    @16
    @6
    cbs
    cfv
    wceq
    wtru
    @16
    cR
    @6
    @6
    eqid
    #
    @16
    eqid
    opprbas
    a1i
    #
    @0
    vr
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    @0
    @20
    @6
    cplusg
    cfv
    #
    co
    wceq
    wtru
    @0
    @16
    wcel
    @20
    @16
    wcel
    wa
    wa
    @21
    @22
    @0
    @20
    @21
    cR
    @6
    @18
    @21
    eqid
    oppradd
    oveqi
    a1i
    #
    deg1propd
    trud
    eqtri
    cB
    cP
    cbs
    cfv
    #
    @7
    cbs
    cfv
    #
    ply1divalg.b
    @24
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    @25
    cP
    @26
    cbs
    ply1divalg.p
    fveq2i
    @27
    @25
    wceq
    wtru
    vq
    vr
    @16
    cR
    @6
    @17
    @19
    @23
    ply1baspropd
    trud
    eqtri
    #
    eqtri
    #
    c.mi
    cP
    csg
    cfv
    #
    @7
    csg
    cfv
    #
    ply1divalg.m
    @30
    @31
    wceq
    wtru
    cP
    @7
    @24
    @25
    wceq
    wtru
    @28
    a1i
    cP
    cplusg
    cfv
    #
    @7
    cplusg
    cfv
    #
    wceq
    wtru
    @32
    @26
    cplusg
    cfv
    #
    @33
    cP
    @26
    cplusg
    ply1divalg.p
    fveq2i
    @34
    @33
    wceq
    wtru
    vq
    vr
    @16
    cR
    @6
    @17
    @19
    @23
    ply1plusgpropd
    trud
    eqtri
    #
    a1i
    grpsubpropd
    trud
    eqtri
    c.0
    cP
    c0g
    cfv
    #
    @7
    c0g
    cfv
    #
    ply1divalg.z
    @36
    @37
    wceq
    wtru
    vq
    vr
    cB
    cP
    @7
    cB
    @24
    wceq
    wtru
    ply1divalg.b
    a1i
    cB
    @25
    wceq
    wtru
    @29
    a1i
    @0
    @20
    @32
    co
    @0
    @20
    @33
    co
    wceq
    wtru
    @0
    cB
    wcel
    #
    @20
    cB
    wcel
    wa
    wa
    @32
    @33
    @0
    @20
    @35
    oveqi
    a1i
    grpidpropd
    trud
    eqtri
    @8
    eqid
    #
    wph
    cR
    crg
    wcel
    #
    @6
    crg
    wcel
    ply1divalg.r1
    cR
    @6
    @18
    opprring
    syl
    ply1divalg.f
    ply1divalg.g1
    ply1divalg.g2
    ply1divalg.g3
    cR
    @6
    cU
    ply1divalg.u
    @18
    opprunit
    ply1divalg
    wph
    @5
    @12
    vq
    cB
    wph
    @38
    wa
    #
    @3
    @11
    @4
    clt
    @41
    @2
    @10
    cD
    @41
    @1
    @9
    cF
    c.mi
    @41
    @9
    @1
    @41
    @40
    cG
    cB
    wcel
    #
    @38
    @9
    @1
    wceq
    wph
    @40
    @38
    ply1divalg.r1
    adantr
    wph
    @42
    @38
    ply1divalg.g1
    adantr
    wph
    @38
    simpr
    cB
    cR
    @6
    @8
    c.xb
    cG
    @0
    cP
    @7
    ply1divalg.p
    @18
    @13
    ply1divalg.t
    @39
    ply1divalg.b
    ply1opprmul
    syl3anc
    eqcomd
    oveq2d
    fveq2d
    breq1d
    reubidva
    mpbird
end
