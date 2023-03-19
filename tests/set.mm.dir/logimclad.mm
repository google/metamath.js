include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cr.mm"
include "wcel.mm"
include "cpi.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cioc.mm"
include "co.mm"
include "logcld.mm"
include "imcld.mm"
include "logimcld.mm"
include "simpld.mm"
include "simprd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "pire.mm"
include "renegcli.mm"
include "rexri.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem logimclad
  let wph: wff ph
  let cX: class X
  assume logimcld.1: |- ( ph -> X e. CC )
  assume logimcld.2: |- ( ph -> X =/= 0 )


  assert |- ( ph -> ( Im ` ( log ` X ) ) e. ( -u _pi (,] _pi ) )

  proof
    wph
    cX
    clog
    cfv
    #
    cim
    cfv
    #
    cr
    wcel
    #
    cpi
    cneg
    #
    @1
    clt
    wbr
    #
    @1
    cpi
    cle
    wbr
    #
    @1
    @3
    cpi
    cioc
    co
    wcel
    #
    wph
    @0
    wph
    cX
    logimcld.1
    logimcld.2
    logcld
    imcld
    wph
    @4
    @5
    wph
    cX
    logimcld.1
    logimcld.2
    logimcld
    #
    simpld
    wph
    @4
    @5
    @7
    simprd
    @3
    cxr
    wcel
    cpi
    cr
    wcel
    @6
    @2
    @4
    @5
    w3a
    wb
    @3
    cpi
    pire
    renegcli
    rexri
    pire
    @3
    cpi
    @1
    elioc2
    mp2an
    syl3anbrc
end
