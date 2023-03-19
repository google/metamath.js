include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelz.mm"
include "zaddcl.mm"
include "sylancl.mm"
include "wa.mm"
include "eluz1i.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "zrei.mm"
include "leadd1.mm"
include "mp3an13.mm"
include "syl.mm"
include "biimpa.mm"
include "sylbi.mm"
include "mp2an.mm"
include "sylanbrc.mm"

theorem eluzaddi
  let cK: class K
  let cM: class M
  let cN: class N
  assume eluzaddi.1: |- M e. ZZ
  assume eluzaddi.2: |- K e. ZZ


  assert |- ( N e. ( ZZ>= ` M ) -> ( N + K ) e. ( ZZ>= ` ( M + K ) ) )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cN
    cK
    caddc
    co
    #
    cz
    wcel
    #
    cM
    cK
    caddc
    co
    #
    @1
    cle
    wbr
    #
    @1
    @3
    cuz
    cfv
    wcel
    @0
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @2
    cM
    cN
    eluzelz
    eluzaddi.2
    cN
    cK
    zaddcl
    sylancl
    @0
    @5
    cM
    cN
    cle
    wbr
    #
    wa
    @4
    cM
    cN
    eluzaddi.1
    eluz1i
    @5
    @7
    @4
    @5
    cN
    cr
    wcel
    #
    @7
    @4
    wb
    #
    cN
    zre
    cM
    cr
    wcel
    @8
    cK
    cr
    wcel
    @9
    cM
    eluzaddi.1
    zrei
    cK
    eluzaddi.2
    zrei
    cM
    cN
    cK
    leadd1
    mp3an13
    syl
    biimpa
    sylbi
    @3
    @1
    cM
    cz
    wcel
    @6
    @3
    cz
    wcel
    eluzaddi.1
    eluzaddi.2
    cM
    cK
    zaddcl
    mp2an
    eluz1i
    sylanbrc
end
