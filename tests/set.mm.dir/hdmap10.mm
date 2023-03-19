include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "c0g.mm"
include "sneq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "wne.mm"
include "wa.mm"
include "cbs.mm"
include "cid.mm"
include "cres.mm"
include "cltrn.mm"
include "cop.mm"
include "chdma1.mm"
include "chvm.mm"
include "chlt.mm"
include "wcel.mm"
include "adantr.mm"
include "eqid.mm"
include "cdif.mm"
include "anim1i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "hdmap10lem.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lspsn0.mm"
include "syl.mm"
include "mapd0.mm"
include "hdmapval0.mm"
include "lcdlmod.mm"
include "eqtr2d.mm"
include "3eqtrd.mm"
include "pm2.61ne.mm"

theorem hdmap10
  let wph: wff ph
  let cC: class C
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  assume hdmap10.h: |- H = ( LHyp ` K )
  assume hdmap10.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap10.v: |- V = ( Base ` U )
  assume hdmap10.n: |- N = ( LSpan ` U )
  assume hdmap10.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap10.l: |- L = ( LSpan ` C )
  assume hdmap10.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap10.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap10.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap10.t: |- ( ph -> T e. V )


  assert |- ( ph -> ( M ` ( N ` { T } ) ) = ( L ` { ( S ` T ) } ) )

  proof
    wph
    cT
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    cT
    cS
    cfv
    #
    csn
    #
    cL
    cfv
    #
    wceq
    cU
    c0g
    cfv
    #
    csn
    #
    cN
    cfv
    #
    cM
    cfv
    #
    @6
    cS
    cfv
    #
    csn
    #
    cL
    cfv
    #
    wceq
    cT
    @6
    cT
    @6
    wceq
    #
    @2
    @9
    @5
    @12
    @13
    @1
    @8
    cM
    @13
    @0
    @7
    cN
    cT
    @6
    sneq
    fveq2d
    fveq2d
    @13
    @4
    @11
    cL
    @13
    @3
    @10
    cT
    @6
    cS
    fveq2
    sneqd
    fveq2d
    eqeq12d
    wph
    cT
    @6
    wne
    #
    wa
    #
    cC
    cC
    cbs
    cfv
    #
    cS
    cT
    cU
    cid
    cK
    cbs
    cfv
    cres
    cid
    cW
    cK
    cltrn
    cfv
    cfv
    cres
    cop
    #
    cH
    cW
    cK
    chdma1
    cfv
    cfv
    #
    cW
    cK
    chvm
    cfv
    cfv
    #
    cK
    cL
    cM
    cN
    cV
    cW
    @6
    hdmap10.h
    hdmap10.u
    hdmap10.v
    hdmap10.n
    hdmap10.c
    hdmap10.l
    hdmap10.m
    hdmap10.s
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @14
    hdmap10.k
    adantr
    @17
    eqid
    @6
    eqid
    #
    @16
    eqid
    @19
    eqid
    @18
    eqid
    @15
    cT
    cV
    wcel
    #
    @14
    wa
    cT
    cV
    @7
    cdif
    wcel
    wph
    @21
    @14
    hdmap10.t
    anim1i
    cT
    cV
    @6
    eldifsn
    sylibr
    hdmap10lem
    wph
    @9
    @7
    cM
    cfv
    cC
    c0g
    cfv
    #
    csn
    #
    @12
    wph
    @8
    @7
    cM
    wph
    cU
    clmod
    wcel
    @8
    @7
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmap10.h
    hdmap10.u
    hdmap10.k
    dvhlmod
    cN
    cU
    @6
    @20
    hdmap10.n
    lspsn0
    syl
    fveq2d
    wph
    cC
    cU
    cH
    cK
    cM
    @6
    cW
    @22
    hdmap10.h
    hdmap10.m
    hdmap10.u
    @20
    hdmap10.c
    @22
    eqid
    #
    hdmap10.k
    mapd0
    wph
    @12
    @23
    cL
    cfv
    #
    @23
    wph
    @11
    @23
    cL
    wph
    @10
    @22
    wph
    cC
    @22
    cS
    cU
    cH
    cK
    cW
    @6
    hdmap10.h
    hdmap10.u
    @20
    hdmap10.c
    @24
    hdmap10.s
    hdmap10.k
    hdmapval0
    sneqd
    fveq2d
    wph
    cC
    clmod
    wcel
    @25
    @23
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap10.h
    hdmap10.c
    hdmap10.k
    lcdlmod
    cL
    cC
    @22
    @24
    hdmap10.l
    lspsn0
    syl
    eqtr2d
    3eqtrd
    pm2.61ne
end
