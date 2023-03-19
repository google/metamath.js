include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "cvv.mm"
include "wb.mm"
include "come.mm"
include "unidmex.mm"
include "ssexd.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "adantr.mm"
include "wceq.mm"
include "inss2.mm"
include "a1i.mm"
include "omess0.mm"
include "oveq1d.mm"
include "cxr.mm"
include "difssd.mm"
include "elpwi.mm"
include "sstrd.mm"
include "adantl.mm"
include "omexrcl.mm"
include "xaddid2.mm"
include "eqtrd.mm"
include "omessle.mm"
include "eqbrtrd.mm"
include "caragenel2d.mm"

theorem caragencmpl
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cO: class O
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragencmpl.o: |- ( ph -> O e. OutMeas )
  assume caragencmpl.x: |- X = U. dom O
  assume caragencmpl.e: |- ( ph -> E C_ X )
  assume caragencmpl.z: |- ( ph -> ( O ` E ) = 0 )
  assume caragencmpl.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> E e. S )

  proof
    wph
    cS
    cE
    cO
    cX
    va
    caragencmpl.o
    caragencmpl.x
    caragencmpl.s
    wph
    cE
    cX
    cpw
    #
    wcel
    #
    cE
    cX
    wss
    #
    caragencmpl.e
    wph
    cE
    cvv
    wcel
    @1
    @2
    wb
    wph
    cE
    cX
    cvv
    wph
    cO
    come
    cX
    caragencmpl.o
    caragencmpl.x
    unidmex
    caragencmpl.e
    ssexd
    cE
    cX
    cvv
    elpwg
    syl
    mpbird
    wph
    va
    cv
    #
    @0
    wcel
    #
    wa
    #
    @3
    cE
    cin
    #
    cO
    cfv
    #
    @3
    cE
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    #
    @9
    @3
    cO
    cfv
    cle
    @5
    @10
    cc0
    @9
    cxad
    co
    #
    @9
    @5
    @7
    cc0
    @9
    cxad
    @5
    cE
    @6
    cO
    cX
    wph
    cO
    come
    wcel
    @4
    caragencmpl.o
    adantr
    #
    caragencmpl.x
    wph
    @2
    @4
    caragencmpl.e
    adantr
    wph
    cE
    cO
    cfv
    cc0
    wceq
    @4
    caragencmpl.z
    adantr
    @6
    cE
    wss
    @5
    @3
    cE
    inss2
    a1i
    omess0
    oveq1d
    @5
    @9
    cxr
    wcel
    @11
    @9
    wceq
    @5
    @8
    cO
    cX
    @12
    caragencmpl.x
    @4
    @8
    cX
    wss
    wph
    @4
    @8
    @3
    cX
    @4
    @3
    cE
    difssd
    #
    @3
    cX
    elpwi
    #
    sstrd
    adantl
    omexrcl
    @9
    xaddid2
    syl
    eqtrd
    @5
    @8
    @3
    cO
    cX
    @12
    caragencmpl.x
    @4
    @3
    cX
    wss
    wph
    @14
    adantl
    @4
    @8
    @3
    wss
    wph
    @13
    adantl
    omessle
    eqbrtrd
    caragenel2d
end
