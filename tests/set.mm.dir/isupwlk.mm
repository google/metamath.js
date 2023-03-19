include "wcel.mm"
include "w3a.mm"
include "cupwlks.mm"
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
include "cpr.mm"
include "wceq.mm"
include "cfzo.mm"
include "wral.mm"
include "copab.mm"
include "df-br.mm"
include "upwlksfval.mm"
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
include "fveq2d.mm"
include "preq12d.mm"
include "eqeqan12d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "opelopabga.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem isupwlk
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
  let vx: setvar x
  assume upwlksfval.v: |- V = ( Vtx ` G )
  assume upwlksfval.i: |- I = ( iEdg ` G )

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
  disjoint k x
  assert |- ( ( G e. W /\ F e. U /\ P e. Z ) -> ( F ( UPWalks ` G ) P <-> ( F e. Word dom I /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. k e. ( 0 ..^ ( # ` F ) ) ( I ` ( F ` k ) ) = { ( P ` k ) , ( P ` ( k + 1 ) ) } ) ) )

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
    cupwlks
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
    @7
    cfv
    #
    cI
    cfv
    #
    @14
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
    cpr
    #
    wceq
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
    cF
    cfv
    #
    cI
    cfv
    #
    @14
    cP
    cfv
    #
    @18
    cP
    cfv
    #
    cpr
    #
    wceq
    #
    vk
    cc0
    @28
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
    @26
    cF
    cP
    @4
    df-br
    @3
    @4
    @25
    @6
    @0
    @1
    @4
    @25
    wceq
    @2
    vf
    vk
    cG
    cI
    cV
    cW
    vp
    upwlksfval.v
    upwlksfval.i
    upwlksfval
    3ad2ant1
    eleq2d
    syl5bb
    @1
    @2
    @26
    @39
    wb
    @0
    @24
    @39
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
    @27
    @13
    @30
    @23
    @38
    @40
    @9
    @27
    wb
    @41
    @7
    cF
    @8
    eleq1
    adantr
    @42
    @11
    @29
    cV
    @12
    cP
    @40
    @41
    simpr
    @40
    @11
    @29
    wceq
    @41
    @40
    @10
    @28
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
    @42
    @21
    @36
    vk
    @22
    @37
    @40
    @22
    @37
    wceq
    @41
    @40
    @10
    @28
    cc0
    cfzo
    @43
    oveq2d
    adantr
    @40
    @41
    @16
    @32
    @20
    @35
    @40
    @15
    @31
    cI
    @14
    @7
    cF
    fveq1
    fveq2d
    @41
    @17
    @33
    @19
    @34
    @14
    @12
    cP
    fveq1
    @18
    @12
    cP
    fveq1
    preq12d
    eqeqan12d
    raleqbidv
    3anbi123d
    opelopabga
    3adant1
    bitrd
end
