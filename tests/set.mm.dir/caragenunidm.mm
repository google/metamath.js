include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "cdm.mm"
include "cuni.mm"
include "come.mm"
include "dmexg.mm"
include "uniexg.mm"
include "3syl.mm"
include "syl5eqel.mm"
include "pwidg.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wss.mm"
include "elpwi.mm"
include "df-ss.mm"
include "biimpi.mm"
include "fveq2d.mm"
include "adantl.mm"
include "c0.mm"
include "ssdif0.mm"
include "sylib.mm"
include "ome0.mm"
include "adantr.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "omecl.mm"
include "sseldi.mm"
include "xaddid1d.mm"
include "eqidd.mm"
include "3eqtrd.mm"
include "carageneld.mm"

theorem caragenunidm
  let wph: wff ph
  let cS: class S
  let cO: class O
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume caragenunidm.o: |- ( ph -> O e. OutMeas )
  assume caragenunidm.x: |- X = U. dom O
  assume caragenunidm.s: |- S = ( CaraGen ` O )


  assert |- ( ph -> X e. S )

  proof
    wph
    cS
    cX
    cO
    cX
    va
    caragenunidm.o
    caragenunidm.x
    caragenunidm.s
    wph
    cX
    cvv
    wcel
    cX
    cX
    cpw
    #
    wcel
    wph
    cX
    cO
    cdm
    #
    cuni
    #
    cvv
    caragenunidm.x
    wph
    cO
    come
    wcel
    #
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    caragenunidm.o
    cO
    come
    dmexg
    @1
    cvv
    uniexg
    3syl
    syl5eqel
    cX
    cvv
    pwidg
    syl
    wph
    va
    cv
    #
    @0
    wcel
    #
    wa
    #
    @4
    cX
    cin
    #
    cO
    cfv
    #
    @4
    cX
    cdif
    #
    cO
    cfv
    #
    cxad
    co
    @4
    cO
    cfv
    #
    cc0
    cxad
    co
    @11
    @11
    @6
    @8
    @11
    @10
    cc0
    cxad
    @5
    @8
    @11
    wceq
    wph
    @5
    @7
    @4
    cO
    @5
    @4
    cX
    wss
    #
    @7
    @4
    wceq
    #
    @4
    cX
    elpwi
    #
    @12
    @13
    @4
    cX
    df-ss
    biimpi
    syl
    fveq2d
    adantl
    @6
    @10
    c0
    cO
    cfv
    #
    cc0
    @5
    @10
    @15
    wceq
    wph
    @5
    @9
    c0
    cO
    @5
    @12
    @9
    c0
    wceq
    @14
    @4
    cX
    ssdif0
    sylib
    fveq2d
    adantl
    wph
    @15
    cc0
    wceq
    @5
    wph
    cO
    caragenunidm.o
    ome0
    adantr
    eqtrd
    oveq12d
    @6
    @11
    @6
    cc0
    cpnf
    cicc
    co
    cxr
    @11
    cc0
    cpnf
    iccssxr
    @6
    @4
    cO
    cX
    wph
    @3
    @5
    caragenunidm.o
    adantr
    caragenunidm.x
    @5
    @12
    wph
    @14
    adantl
    omecl
    sseldi
    xaddid1d
    @6
    @11
    eqidd
    3eqtrd
    carageneld
end
