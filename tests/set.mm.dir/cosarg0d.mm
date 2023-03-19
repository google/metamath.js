include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "ccos.mm"
include "cc0.mm"
include "wceq.mm"
include "cre.mm"
include "cabs.mm"
include "cdiv.mm"
include "co.mm"
include "cosargd.mm"
include "eqeq1d.mm"
include "recld.mm"
include "recnd.mm"
include "abscld.mm"
include "absne0d.mm"
include "diveq0ad.mm"
include "bitrd.mm"

theorem cosarg0d
  let wph: wff ph
  let cX: class X
  assume cosargd.1: |- ( ph -> X e. CC )
  assume cosargd.2: |- ( ph -> X =/= 0 )


  assert |- ( ph -> ( ( cos ` ( Im ` ( log ` X ) ) ) = 0 <-> ( Re ` X ) = 0 ) )

  proof
    wph
    cX
    clog
    cfv
    cim
    cfv
    ccos
    cfv
    #
    cc0
    wceq
    cX
    cre
    cfv
    #
    cX
    cabs
    cfv
    #
    cdiv
    co
    #
    cc0
    wceq
    @1
    cc0
    wceq
    wph
    @0
    @3
    cc0
    wph
    cX
    cosargd.1
    cosargd.2
    cosargd
    eqeq1d
    wph
    @1
    @2
    wph
    @1
    wph
    cX
    cosargd.1
    recld
    recnd
    wph
    @2
    wph
    cX
    cosargd.1
    abscld
    recnd
    wph
    cX
    cosargd.1
    cosargd.2
    absne0d
    diveq0ad
    bitrd
end
