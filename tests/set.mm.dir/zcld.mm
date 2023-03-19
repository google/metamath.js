include "cz.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "cdif.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cioo.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "wa.mm"
include "elioore.mm"
include "adantl.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "eliooord.mm"
include "btwnnz.mm"
include "3expb.mm"
include "sylan2.mm"
include "eldifd.mm"
include "rexlimiva.mm"
include "cfl.mm"
include "eldifi.mm"
include "flcld.mm"
include "cle.mm"
include "wne.mm"
include "flle.mm"
include "syl.mm"
include "eldifn.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "zred.mm"
include "ltlend.mm"
include "mpbir2and.mm"
include "flltp1.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "rexrd.mm"
include "peano2re.mm"
include "elioo2.mm"
include "mpbir3and.mm"
include "wceq.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "impbii.mm"
include "bitri.mm"
include "eqriv.mm"
include "ctop.mm"
include "wral.mm"
include "crn.mm"
include "ctg.mm"
include "retop.mm"
include "eqeltri.mm"
include "iooretop.mm"
include "eleqtrri.mm"
include "rgenw.mm"
include "iunopn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "wss.mm"
include "zssre.mm"
include "cuni.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "iscld2.mm"
include "mpbir.mm"

theorem zcld
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  assume zcld.1: |- J = ( topGen ` ran (,) )


  assert |- ZZ e. ( Clsd ` J )

  proof
    cz
    cJ
    ccld
    cfv
    wcel
    #
    cr
    cz
    cdif
    #
    cJ
    wcel
    #
    vx
    cz
    vx
    cv
    #
    @3
    c1
    caddc
    co
    #
    cioo
    co
    #
    ciun
    #
    @1
    cJ
    vy
    @6
    @1
    vy
    cv
    #
    @6
    wcel
    @7
    @5
    wcel
    #
    vx
    cz
    wrex
    #
    @7
    @1
    wcel
    #
    vx
    @7
    cz
    @5
    eliun
    @9
    @10
    @8
    @10
    vx
    cz
    @3
    cz
    wcel
    #
    @8
    wa
    @7
    cr
    cz
    @8
    @7
    cr
    wcel
    #
    @11
    @7
    @3
    @4
    elioore
    adantl
    @8
    @11
    @3
    @7
    clt
    wbr
    #
    @7
    @4
    clt
    wbr
    #
    wa
    @7
    cz
    wcel
    wn
    #
    @7
    @3
    @4
    eliooord
    @11
    @13
    @14
    @15
    @3
    @7
    btwnnz
    3expb
    sylan2
    eldifd
    rexlimiva
    @10
    @7
    cfl
    cfv
    #
    cz
    wcel
    #
    @7
    @16
    @16
    c1
    caddc
    co
    #
    cioo
    co
    #
    wcel
    #
    @9
    @10
    @7
    @7
    cr
    cz
    eldifi
    #
    flcld
    #
    @10
    @20
    @12
    @16
    @7
    clt
    wbr
    #
    @7
    @18
    clt
    wbr
    #
    @21
    @10
    @23
    @16
    @7
    cle
    wbr
    #
    @7
    @16
    wne
    @10
    @12
    @25
    @21
    @7
    flle
    syl
    @10
    @16
    @7
    @10
    @17
    @15
    @16
    @7
    wne
    @22
    @7
    cr
    cz
    eldifn
    @16
    @7
    cz
    nelne2
    syl2anc
    necomd
    @10
    @16
    @7
    @10
    @16
    @22
    zred
    #
    @21
    ltlend
    mpbir2and
    @10
    @12
    @24
    @21
    @7
    flltp1
    syl
    @10
    @16
    cxr
    wcel
    @18
    cxr
    wcel
    @20
    @12
    @23
    @24
    w3a
    wb
    @10
    @16
    @26
    rexrd
    @10
    @18
    @10
    @16
    cr
    wcel
    @18
    cr
    wcel
    @26
    @16
    peano2re
    syl
    rexrd
    @16
    @18
    @7
    elioo2
    syl2anc
    mpbir3and
    @8
    @20
    vx
    @16
    cz
    @3
    @16
    wceq
    #
    @5
    @19
    @7
    @27
    @3
    @16
    @4
    @18
    cioo
    @27
    id
    @3
    @16
    c1
    caddc
    oveq1
    oveq12d
    eleq2d
    rspcev
    syl2anc
    impbii
    bitri
    eqriv
    cJ
    ctop
    wcel
    #
    @5
    cJ
    wcel
    #
    vx
    cz
    wral
    @6
    cJ
    wcel
    cJ
    cioo
    crn
    ctg
    cfv
    #
    ctop
    zcld.1
    retop
    eqeltri
    #
    @29
    vx
    cz
    @5
    @30
    cJ
    @3
    @4
    iooretop
    zcld.1
    eleqtrri
    rgenw
    vx
    cz
    @5
    cJ
    iunopn
    mp2an
    eqeltrri
    @28
    cz
    cr
    wss
    @0
    @2
    wb
    @31
    zssre
    cz
    cJ
    cr
    cr
    @30
    cuni
    cJ
    cuni
    uniretop
    cJ
    @30
    zcld.1
    unieqi
    eqtr4i
    iscld2
    mp2an
    mpbir
end
