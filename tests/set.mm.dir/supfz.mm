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
include "eluzelz.mm"
include "eluzfz2.mm"
include "cv.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "elfzle2.mm"
include "adantl.mm"
include "wb.mm"
include "elfzelz.mm"
include "zred.mm"
include "eluzelre.mm"
include "lenlt.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "supmax.mm"

theorem supfz
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> sup ( ( M ... N ) , ZZ , < ) = N )

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
    cN
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
    eluzelz
    cM
    cN
    eluzfz2
    @0
    vx
    cv
    #
    @1
    wcel
    #
    wa
    @3
    cN
    cle
    wbr
    #
    cN
    @3
    clt
    wbr
    wn
    #
    @4
    @5
    @0
    @3
    cM
    cN
    elfzle2
    adantl
    @4
    @3
    cr
    wcel
    cN
    cr
    wcel
    @5
    @6
    wb
    @0
    @4
    @3
    @3
    cM
    cN
    elfzelz
    zred
    cM
    cN
    eluzelre
    @3
    cN
    lenlt
    syl2anr
    mpbid
    supmax
end
