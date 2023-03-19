include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cfz.mm"
include "co.mm"
include "clt.mm"
include "ccnv.mm"
include "wor.mm"
include "cr.mm"
include "wss.mm"
include "zssre.mm"
include "ltso.mm"
include "soss.mm"
include "mp2.mm"
include "cnvso.mm"
include "mpbi.mm"
include "a1i.mm"
include "eluzel2.mm"
include "eluzfz1.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "elfzle1.mm"
include "adantl.mm"
include "wb.mm"
include "zred.mm"
include "elfzelz.mm"
include "lenlt.mm"
include "syl2an.mm"
include "mpbid.mm"
include "brcnvg.mm"
include "notbid.mm"
include "sylan.mm"
include "mpbird.mm"
include "supmax.mm"

theorem inffzOLD
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( N e. ( ZZ>= ` M ) -> sup ( ( M ... N ) , ZZ , `' < ) = M )

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
    ccnv
    #
    cz
    @2
    wor
    #
    @0
    cz
    clt
    wor
    #
    @3
    cz
    cr
    wss
    cr
    clt
    wor
    @4
    zssre
    ltso
    cz
    cr
    clt
    soss
    mp2
    cz
    clt
    cnvso
    mpbi
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
    #
    cM
    @6
    @2
    wbr
    #
    wn
    #
    @6
    cM
    clt
    wbr
    #
    wn
    #
    @8
    cM
    @6
    cle
    wbr
    #
    @12
    @7
    @13
    @0
    @6
    cM
    cN
    elfzle1
    adantl
    @0
    cM
    cr
    wcel
    @6
    cr
    wcel
    @13
    @12
    wb
    @7
    @0
    cM
    @5
    zred
    @7
    @6
    @6
    cM
    cN
    elfzelz
    zred
    cM
    @6
    lenlt
    syl2an
    mpbid
    @0
    cM
    cz
    wcel
    #
    @7
    @10
    @12
    wb
    @5
    @14
    @7
    wa
    @9
    @11
    cM
    @6
    cz
    @1
    clt
    brcnvg
    notbid
    sylan
    mpbird
    supmax
end
