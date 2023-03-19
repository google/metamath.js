include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "cgsu.mm"
include "w3a.mm"
include "cmap.mm"
include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "cfsupp.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "jctir.mm"
include "fsuppmapnn0ub.mm"
include "sylc.mm"
include "eqidd.mm"
include "simpr.mm"
include "ccmn.mm"
include "adantr.mm"
include "eqid.mm"
include "fsfnn0gsumfsffz.mm"
include "imp.mm"
include "wss.mm"
include "fz0ssnn0.mm"
include "elmapssres.mm"
include "sylancl.mm"
include "wb.mm"
include "eqeq1.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "3anbi13d.mm"
include "adantl.mm"
include "rspcedv.mm"
include "mp3and.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem nn0gsumfz
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vs: setvar s
  assume nn0gsumfz.b: |- B = ( Base ` G )
  assume nn0gsumfz.0: |- .0. = ( 0g ` G )
  assume nn0gsumfz.g: |- ( ph -> G e. CMnd )
  assume nn0gsumfz.f: |- ( ph -> F e. ( B ^m NN0 ) )
  assume nn0gsumfz.y: |- ( ph -> F finSupp .0. )

  disjoint B f
  disjoint F f
  disjoint F s
  disjoint F x
  disjoint f s
  disjoint f x
  disjoint s x
  disjoint G f
  disjoint .0. f
  disjoint .0. s
  disjoint .0. x
  disjoint f ph
  disjoint ph s
  assert |- ( ph -> E. s e. NN0 E. f e. ( B ^m ( 0 ... s ) ) ( f = ( F |` ( 0 ... s ) ) /\ A. x e. NN0 ( s < x -> ( F ` x ) = .0. ) /\ ( G gsum F ) = ( G gsum f ) ) )

  proof
    wph
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    @1
    cF
    cfv
    c.0
    wceq
    wi
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    vf
    cv
    #
    cF
    cc0
    @0
    cfz
    co
    #
    cres
    #
    wceq
    #
    @2
    cG
    cF
    cgsu
    co
    #
    cG
    @4
    cgsu
    co
    #
    wceq
    #
    w3a
    #
    vf
    cB
    @5
    cmap
    co
    #
    wrex
    #
    vs
    cn0
    wrex
    wph
    cF
    cB
    cn0
    cmap
    co
    wcel
    #
    c.0
    cvv
    wcel
    #
    wa
    cF
    c.0
    cfsupp
    wbr
    @3
    wph
    @14
    @15
    nn0gsumfz.f
    c.0
    cG
    c0g
    cfv
    cvv
    nn0gsumfz.0
    cG
    c0g
    fvex
    eqeltri
    jctir
    nn0gsumfz.y
    vx
    cB
    vs
    cF
    cvv
    c.0
    fsuppmapnn0ub
    sylc
    wph
    @2
    @13
    vs
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @2
    @13
    @17
    @2
    wa
    #
    @6
    @6
    wceq
    #
    @2
    @8
    cG
    @6
    cgsu
    co
    #
    wceq
    #
    @13
    @18
    @6
    eqidd
    @17
    @2
    simpr
    @17
    @2
    @21
    @17
    vx
    cB
    @0
    cF
    cG
    @6
    c.0
    nn0gsumfz.b
    nn0gsumfz.0
    wph
    cG
    ccmn
    wcel
    @16
    nn0gsumfz.g
    adantr
    wph
    @14
    @16
    nn0gsumfz.f
    adantr
    #
    wph
    @16
    simpr
    @6
    eqid
    fsfnn0gsumfsffz
    imp
    @18
    @11
    @19
    @2
    @21
    w3a
    #
    vf
    @6
    @12
    @18
    @14
    @5
    cn0
    wss
    @6
    @12
    wcel
    @17
    @14
    @2
    @22
    adantr
    @0
    fz0ssnn0
    cF
    cB
    cn0
    @5
    elmapssres
    sylancl
    @7
    @11
    @23
    wb
    @18
    @7
    @7
    @19
    @10
    @21
    @2
    @4
    @6
    @6
    eqeq1
    @7
    @9
    @20
    @8
    @4
    @6
    cG
    cgsu
    oveq2
    eqeq2d
    3anbi13d
    adantl
    rspcedv
    mp3and
    ex
    reximdva
    mpd
end
