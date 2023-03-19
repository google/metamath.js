include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "wor.mm"
include "cr.mm"
include "wss.mm"
include "zssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "eluzel2.mm"
include "eluzfz1.mm"
include "cv.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "elfzle1.mm"
include "adantl.mm"
include "wb.mm"
include "zred.mm"
include "elfzelz.mm"
include "lenlt.mm"
include "syl2an.mm"
include "mpbid.mm"
include "infmin.mm"

theorem inffz
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> inf ( ( M ... N ) , ZZ , < ) = M )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    vx
    cz
    cM
    cN
    cfz
    co
    #
    cM
    clt
    cz
    clt
    wor
    #
    @0
    cz
    cr
    wss
    cr
    clt
    wor
    @2
    zssre
    ltso
    cz
    cr
    clt
    soss
    mp2
    a1i
    cM
    cN
    eluzel2
    #
    cM
    cN
    eluzfz1
    @0
    vx
    cv
    #
    @1
    wcel
    #
    wa
    cM
    @4
    cle
    wbr
    #
    @4
    cM
    clt
    wbr
    wn
    #
    @5
    @6
    @0
    @4
    cM
    cN
    elfzle1
    adantl
    @0
    cM
    cr
    wcel
    @4
    cr
    wcel
    @6
    @7
    wb
    @5
    @0
    cM
    @3
    zred
    @5
    @4
    @4
    cM
    cN
    elfzelz
    zred
    cM
    @4
    lenlt
    syl2an
    mpbid
    infmin
end
