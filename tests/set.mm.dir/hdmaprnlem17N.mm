include "cv.mm"
include "crn.mm"
include "wcel.mm"
include "eleq1.mm"
include "wne.mm"
include "wa.mm"
include "chlt.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "hdmaprnlem16N.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "hdmapval0.mm"
include "wfn.mm"
include "hdmapfnN.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmod0vcl.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "pm2.61ne.mm"

theorem hdmaprnlem17N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  assume hdmaprnlem15.h: |- H = ( LHyp ` K )
  assume hdmaprnlem15.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaprnlem15.v: |- V = ( Base ` U )
  assume hdmaprnlem15.n: |- N = ( LSpan ` U )
  assume hdmaprnlem15.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmaprnlem15.d: |- D = ( Base ` C )
  assume hdmaprnlem15.q: |- .0. = ( 0g ` C )
  assume hdmaprnlem15.l: |- L = ( LSpan ` C )
  assume hdmaprnlem15.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmaprnlem15.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaprnlem15.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaprnlem17.se: |- ( ph -> s e. D )


  assert |- ( ph -> s e. ran S )

  proof
    wph
    vs
    cv
    #
    cS
    crn
    #
    wcel
    c.0
    @1
    wcel
    @0
    c.0
    @0
    c.0
    @1
    eleq1
    wph
    @0
    c.0
    wne
    #
    wa
    #
    cC
    cD
    cS
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    c.0
    vs
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.v
    hdmaprnlem15.n
    hdmaprnlem15.c
    hdmaprnlem15.d
    hdmaprnlem15.q
    hdmaprnlem15.l
    hdmaprnlem15.m
    hdmaprnlem15.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @2
    hdmaprnlem15.k
    adantr
    @3
    @0
    cD
    wcel
    #
    @2
    wa
    @0
    cD
    c.0
    csn
    cdif
    wcel
    wph
    @4
    @2
    hdmaprnlem17.se
    anim1i
    @0
    cD
    c.0
    eldifsn
    sylibr
    hdmaprnlem16N
    wph
    cU
    c0g
    cfv
    #
    cS
    cfv
    #
    c.0
    @1
    wph
    cC
    c.0
    cS
    cU
    cH
    cK
    cW
    @5
    hdmaprnlem15.h
    hdmaprnlem15.u
    @5
    eqid
    #
    hdmaprnlem15.c
    hdmaprnlem15.q
    hdmaprnlem15.s
    hdmaprnlem15.k
    hdmapval0
    wph
    cS
    cV
    wfn
    @5
    cV
    wcel
    #
    @6
    @1
    wcel
    wph
    cS
    cU
    cH
    cK
    cV
    cW
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.v
    hdmaprnlem15.s
    hdmaprnlem15.k
    hdmapfnN
    wph
    cU
    clmod
    wcel
    @8
    wph
    cU
    cH
    cK
    cW
    hdmaprnlem15.h
    hdmaprnlem15.u
    hdmaprnlem15.k
    dvhlmod
    cV
    cU
    @5
    hdmaprnlem15.v
    @7
    lmod0vcl
    syl
    cV
    @5
    cS
    fnfvelrn
    syl2anc
    eqeltrrd
    pm2.61ne
end
