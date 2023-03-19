include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wo.mm"
include "wne.mm"
include "cc0.mm"
include "cle.mm"
include "c1.mm"
include "cr.mm"
include "wcel.mm"
include "zrei.mm"
include "0re.mm"
include "lelttric.mm"
include "mp2an.mm"
include "cz.mm"
include "wb.mm"
include "zgt0ge1.mm"
include "ax-mp.mm"
include "orbi2i.mm"
include "mpbi.mm"
include "cneg.mm"
include "le0neg1.mm"
include "nngt0i.mm"
include "nnrei.mm"
include "lttri.mm"
include "mpan.mm"
include "ltlei.mm"
include "syl.mm"
include "renegcli.mm"
include "mulge0i.mm"
include "sylan2.mm"
include "sylanb.mm"
include "expcom.mm"
include "remulcli.mm"
include "recni.mm"
include "mulneg1i.mm"
include "breq2i.mm"
include "bitr4i.mm"
include "syl6ibr.mm"
include "lelttri.mm"
include "mpan2.mm"
include "syl6.mm"
include "wa.mm"
include "lemulge12.mm"
include "mpanl12.mm"
include "sylan.mm"
include "ex.mm"
include "ltletri.mm"
include "syld.mm"
include "orim12d.mm"
include "mpi.mm"
include "lttri2i.mm"
include "sylibr.mm"

theorem dvdslelem
  let cK: class K
  let cM: class M
  let cN: class N
  assume dvdslelem.1: |- M e. ZZ
  assume dvdslelem.2: |- N e. NN
  assume dvdslelem.3: |- K e. ZZ


  assert |- ( N < M -> ( K x. M ) =/= N )

  proof
    cN
    cM
    clt
    wbr
    #
    cK
    cM
    cmul
    co
    #
    cN
    clt
    wbr
    #
    cN
    @1
    clt
    wbr
    #
    wo
    #
    @1
    cN
    wne
    @0
    cK
    cc0
    cle
    wbr
    #
    c1
    cK
    cle
    wbr
    #
    wo
    #
    @4
    @5
    cc0
    cK
    clt
    wbr
    #
    wo
    #
    @7
    cK
    cr
    wcel
    #
    cc0
    cr
    wcel
    @9
    cK
    dvdslelem.3
    zrei
    #
    0re
    cK
    cc0
    lelttric
    mp2an
    @8
    @6
    @5
    cK
    cz
    wcel
    @8
    @6
    wb
    dvdslelem.3
    cK
    zgt0ge1
    ax-mp
    orbi2i
    mpbi
    @0
    @5
    @2
    @6
    @3
    @0
    @5
    @1
    cc0
    cle
    wbr
    #
    @2
    @0
    @5
    cc0
    cK
    cneg
    #
    cM
    cmul
    co
    #
    cle
    wbr
    #
    @12
    @5
    @0
    @15
    @5
    cc0
    @13
    cle
    wbr
    #
    @0
    @15
    @10
    @5
    @16
    wb
    @11
    cK
    le0neg1
    ax-mp
    @0
    @16
    cc0
    cM
    cle
    wbr
    #
    @15
    @0
    cc0
    cM
    clt
    wbr
    #
    @17
    cc0
    cN
    clt
    wbr
    #
    @0
    @18
    cN
    dvdslelem.2
    nngt0i
    #
    cc0
    cN
    cM
    0re
    cN
    dvdslelem.2
    nnrei
    #
    cM
    dvdslelem.1
    zrei
    #
    lttri
    mpan
    cc0
    cM
    0re
    @22
    ltlei
    syl
    #
    @13
    cM
    cK
    @11
    renegcli
    @22
    mulge0i
    sylan2
    sylanb
    expcom
    @12
    cc0
    @1
    cneg
    #
    cle
    wbr
    #
    @15
    @1
    cr
    wcel
    @12
    @25
    wb
    cK
    cM
    @11
    @22
    remulcli
    #
    @1
    le0neg1
    ax-mp
    @14
    @24
    cc0
    cle
    cK
    cM
    cK
    @11
    recni
    cM
    @22
    recni
    mulneg1i
    breq2i
    bitr4i
    syl6ibr
    @12
    @19
    @2
    @20
    @1
    cc0
    cN
    @26
    0re
    @21
    lelttri
    mpan2
    syl6
    @0
    @6
    cM
    @1
    cle
    wbr
    #
    @3
    @0
    @6
    @27
    @0
    @17
    @6
    @27
    @23
    cM
    cr
    wcel
    @10
    @17
    @6
    wa
    @27
    @22
    @11
    cM
    cK
    lemulge12
    mpanl12
    sylan
    ex
    @0
    @27
    @3
    cN
    cM
    @1
    @21
    @22
    @26
    ltletri
    ex
    syld
    orim12d
    mpi
    @1
    cN
    @26
    @21
    lttri2i
    sylibr
end
