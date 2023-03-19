include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cmin.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "eluzelz.mm"
include "zsubcl.mm"
include "sylancl.mm"
include "wa.mm"
include "zaddcl.mm"
include "mp2an.mm"
include "eluz1i.mm"
include "cr.mm"
include "wb.mm"
include "zre.mm"
include "zrei.mm"
include "leaddsub.mm"
include "mp3an12.mm"
include "syl.mm"
include "biimpa.mm"
include "sylbi.mm"
include "sylanbrc.mm"

theorem eluzsubi
  let cK: class K
  let cM: class M
  let cN: class N
  assume eluzaddi.1: |- M e. ZZ
  assume eluzaddi.2: |- K e. ZZ


  assert |- ( N e. ( ZZ>= ` ( M + K ) ) -> ( N - K ) e. ( ZZ>= ` M ) )

  proof
    cN
    cM
    cK
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    cN
    cK
    cmin
    co
    #
    cz
    wcel
    #
    cM
    @2
    cle
    wbr
    #
    @2
    cM
    cuz
    cfv
    wcel
    @1
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @3
    @0
    cN
    eluzelz
    eluzaddi.2
    cN
    cK
    zsubcl
    sylancl
    @1
    @5
    @0
    cN
    cle
    wbr
    #
    wa
    @4
    @0
    cN
    cM
    cz
    wcel
    @6
    @0
    cz
    wcel
    eluzaddi.1
    eluzaddi.2
    cM
    cK
    zaddcl
    mp2an
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
    cK
    cr
    wcel
    @8
    @9
    cM
    eluzaddi.1
    zrei
    cK
    eluzaddi.2
    zrei
    cM
    cK
    cN
    leaddsub
    mp3an12
    syl
    biimpa
    sylbi
    cM
    @2
    eluzaddi.1
    eluz1i
    sylanbrc
end
