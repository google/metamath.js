include "cv.mm"
include "cip.mm"
include "cfv.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "cbs.mm"
include "crab.mm"
include "chdma.mm"
include "hlhilbase.mm"
include "rabeq.mm"
include "syl.mm"
include "wcel.mm"
include "wa.mm"
include "eqid.mm"
include "chlt.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wss.mm"
include "adantr.mm"
include "sselda.mm"
include "hlhilipval.mm"
include "hlhils0.mm"
include "eqcomd.mm"
include "eqeq12d.mm"
include "ralbidva.mm"
include "rabbidva.mm"
include "eqtr3d.mm"
include "sseqtrd.mm"
include "ocvval.mm"
include "hdmapoc.mm"
include "3eqtr4d.mm"

theorem hlhilocv
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hlhil0.h: |- H = ( LHyp ` K )
  assume hlhil0.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhil0.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhil0.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilocv.v: |- V = ( Base ` L )
  assume hlhilocv.n: |- N = ( ( ocH ` K ) ` W )
  assume hlhilocv.o: |- O = ( ocv ` U )
  assume hlhilocv.x: |- ( ph -> X C_ V )


  assert |- ( ph -> ( O ` X ) = ( N ` X ) )

  proof
    wph
    vy
    cv
    #
    vz
    cv
    #
    cU
    cip
    cfv
    #
    co
    #
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cU
    cbs
    cfv
    #
    crab
    #
    @0
    @1
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    cfv
    #
    cL
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vz
    cX
    wral
    #
    vy
    cV
    crab
    #
    cX
    cO
    cfv
    #
    cX
    cN
    cfv
    wph
    @7
    vy
    cV
    crab
    #
    @9
    @16
    wph
    cV
    @8
    wceq
    @18
    @9
    wceq
    wph
    cU
    cH
    cK
    cL
    cV
    cW
    hlhil0.h
    hlhil0.u
    hlhil0.k
    hlhil0.l
    hlhilocv.v
    hlhilbase
    #
    @7
    vy
    cV
    @8
    rabeq
    syl
    wph
    @7
    @15
    vy
    cV
    wph
    @0
    cV
    wcel
    #
    wa
    #
    @6
    @14
    vz
    cX
    @21
    @1
    cX
    wcel
    #
    wa
    #
    @3
    @11
    @5
    @13
    @23
    @10
    cU
    cH
    @2
    cK
    cL
    cV
    cW
    @0
    @1
    hlhil0.h
    hlhil0.l
    hlhilocv.v
    @10
    eqid
    #
    hlhil0.u
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @20
    @22
    hlhil0.k
    ad2antrr
    @2
    eqid
    #
    wph
    @20
    @22
    simplr
    @21
    cX
    cV
    @1
    wph
    cX
    cV
    wss
    @20
    hlhilocv.x
    adantr
    sselda
    hlhilipval
    wph
    @5
    @13
    wceq
    @20
    @22
    wph
    @13
    @5
    wph
    @4
    @12
    cU
    cH
    cK
    cL
    cW
    @13
    hlhil0.h
    hlhil0.l
    @12
    eqid
    #
    hlhil0.u
    @4
    eqid
    #
    hlhil0.k
    @13
    eqid
    #
    hlhils0
    eqcomd
    ad2antrr
    eqeq12d
    ralbidva
    rabbidva
    eqtr3d
    wph
    cX
    @8
    wss
    @17
    @9
    wceq
    wph
    cX
    cV
    @8
    hlhilocv.x
    @19
    sseqtrd
    vy
    vz
    cX
    @4
    @2
    cO
    @8
    cU
    @5
    @8
    eqid
    @25
    @27
    @5
    eqid
    hlhilocv.o
    ocvval
    syl
    wph
    vy
    vz
    @12
    @10
    cL
    cH
    cK
    cN
    cV
    cW
    cX
    @13
    hlhil0.h
    hlhil0.l
    hlhilocv.v
    @26
    @28
    hlhilocv.n
    @24
    hlhil0.k
    hlhilocv.x
    hdmapoc
    3eqtr4d
end
