include "wcel.mm"
include "w3a.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cop.mm"
include "cv.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "copab.mm"
include "df-br.mm"
include "wksfval.mm"
include "3ad2ant1.mm"
include "eleq2d.mm"
include "syl5bb.mm"
include "wb.mm"
include "wa.mm"
include "eleq1.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "feq12d.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eqeqan12d.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "opelopabga.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem iswlk
  let cP: class P
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vp: setvar p
  assume wksfval.v: |- V = ( Vtx ` G )
  assume wksfval.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint F k
  disjoint P k
  disjoint G f
  disjoint G g
  disjoint G p
  disjoint f g
  disjoint f k
  disjoint f p
  disjoint g k
  disjoint g p
  disjoint k p
  disjoint I f
  disjoint I g
  disjoint I p
  disjoint V g
  disjoint V p
  disjoint W f
  disjoint W g
  disjoint F f
  disjoint F p
  disjoint P f
  disjoint P p
  disjoint V f
  assert |- ( ( G e. W /\ F e. U /\ P e. Z ) -> ( F ( Walks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) if- ( ( P ` k ) = ( P ` ( k + 1 ) ) , ( I ` ( F ` k ) ) = { ( P ` k ) } , { ( P ` k ) , ( P ` ( k + 1 ) ) } C_ ( I ` ( F ` k ) ) ) ) ) )

  proof
    cG
    cW
    wcel
    #
    cF
    cU
    wcel
    #
    cP
    cZ
    wcel
    #
    w3a
    #
    cF
    cP
    cG
    cwlks
    cfv
    #
    wbr
    #
    cF
    cP
    cop
    #
    vf
    cv
    #
    cI
    cdm
    cword
    #
    wcel
    #
    cc0
    @7
    chash
    cfv
    #
    cfz
    co
    #
    cV
    vp
    cv
    #
    wf
    #
    vk
    cv
    #
    @12
    cfv
    #
    @14
    c1
    caddc
    co
    #
    @12
    cfv
    #
    wceq
    #
    @14
    @7
    cfv
    #
    cI
    cfv
    #
    @15
    csn
    #
    wceq
    #
    @15
    @17
    cpr
    #
    @20
    wss
    #
    wif
    #
    vk
    cc0
    @10
    cfzo
    co
    #
    wral
    #
    w3a
    #
    vf
    vp
    copab
    #
    wcel
    #
    cF
    @8
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    @14
    cP
    cfv
    #
    @16
    cP
    cfv
    #
    wceq
    #
    @14
    cF
    cfv
    #
    cI
    cfv
    #
    @35
    csn
    #
    wceq
    #
    @35
    @36
    cpr
    #
    @39
    wss
    #
    wif
    #
    vk
    cc0
    @32
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @5
    @6
    @4
    wcel
    @3
    @30
    cF
    cP
    @4
    df-br
    @3
    @4
    @29
    @6
    @0
    @1
    @4
    @29
    wceq
    @2
    vf
    vk
    cG
    cI
    cV
    cW
    vp
    wksfval.v
    wksfval.i
    wksfval
    3ad2ant1
    eleq2d
    syl5bb
    @1
    @2
    @30
    @47
    wb
    @0
    @28
    @47
    vf
    vp
    cF
    cP
    cU
    cZ
    @7
    cF
    wceq
    #
    @12
    cP
    wceq
    #
    wa
    #
    @9
    @31
    @13
    @34
    @27
    @46
    @48
    @9
    @31
    wb
    @49
    @7
    cF
    @8
    eleq1
    adantr
    @50
    @11
    @33
    cV
    @12
    cP
    @48
    @49
    simpr
    @48
    @11
    @33
    wceq
    @49
    @48
    @10
    @32
    cc0
    cfz
    @7
    cF
    chash
    fveq2
    #
    oveq2d
    adantr
    feq12d
    @50
    @25
    @44
    vk
    @26
    @45
    @48
    @26
    @45
    wceq
    @49
    @48
    @10
    @32
    cc0
    cfzo
    @51
    oveq2d
    adantr
    @50
    @18
    @22
    @24
    @37
    @41
    @43
    @49
    @18
    @37
    wb
    @48
    @49
    @15
    @35
    @17
    @36
    @14
    @12
    cP
    fveq1
    #
    @16
    @12
    cP
    fveq1
    #
    eqeq12d
    adantl
    @48
    @49
    @20
    @39
    @21
    @40
    @48
    @19
    @38
    cI
    @14
    @7
    cF
    fveq1
    fveq2d
    #
    @49
    @15
    @35
    @52
    sneqd
    eqeqan12d
    @50
    @23
    @42
    @20
    @39
    @49
    @23
    @42
    wceq
    @48
    @49
    @15
    @35
    @17
    @36
    @52
    @53
    preq12d
    adantl
    @48
    @20
    @39
    wceq
    @49
    @54
    adantr
    sseq12d
    ifpbi123d
    raleqbidv
    3anbi123d
    opelopabga
    3adant1
    bitrd
end
