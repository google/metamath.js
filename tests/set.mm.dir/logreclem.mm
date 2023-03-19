include "clog.mm"
include "crn.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cpi.mm"
include "wceq.mm"
include "cneg.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "cc.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "w3a.mm"
include "logrncn.mm"
include "adantr.mm"
include "negcld.mm"
include "ellogrn.mm"
include "biimpi.mm"
include "simp3d.mm"
include "cr.mm"
include "wi.mm"
include "imcl.mm"
include "pire.mm"
include "leneg.mm"
include "biimpd.mm"
include "sylancl.mm"
include "sylc.mm"
include "renegcli.mm"
include "a1i.mm"
include "renegcld.mm"
include "leloed.mm"
include "orcomd.mm"
include "orcanai.mm"
include "simp2d.mm"
include "ltnegcon1.mm"
include "sylancr.mm"
include "ltle.mm"
include "syl.mm"
include "mpd.mm"
include "wb.mm"
include "imneg.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "mpbir2and.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "sylibr.mm"
include "ex.mm"
include "orrd.mm"
include "recn.mm"
include "anim12i.mm"
include "neg11.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "orbi1d.mm"
include "mpbid.mm"

theorem logreclem
  let cA: class A


  assert |- ( ( A e. ran log /\ -. ( Im ` A ) = _pi ) -> -u A e. ran log )

  proof
    cA
    clog
    crn
    #
    wcel
    #
    cA
    cim
    cfv
    #
    cpi
    wceq
    #
    cA
    cneg
    #
    @0
    wcel
    #
    @1
    cpi
    cneg
    #
    @2
    cneg
    #
    wceq
    #
    @5
    wo
    @3
    @5
    wo
    @1
    @8
    @5
    @1
    @8
    wn
    #
    @5
    @1
    @9
    wa
    #
    @4
    cc
    wcel
    #
    @6
    @4
    cim
    cfv
    #
    clt
    wbr
    #
    @12
    cpi
    cle
    wbr
    #
    w3a
    #
    @5
    @10
    @11
    @13
    @14
    wa
    #
    @15
    @10
    cA
    @1
    cA
    cc
    wcel
    #
    @9
    cA
    logrncn
    #
    adantr
    #
    negcld
    @10
    @16
    @6
    @7
    clt
    wbr
    #
    @7
    cpi
    cle
    wbr
    #
    @1
    @8
    @20
    @1
    @20
    @8
    @1
    @17
    @6
    @7
    cle
    wbr
    #
    @20
    @8
    wo
    #
    @18
    @1
    @17
    @2
    cpi
    cle
    wbr
    #
    @22
    @18
    @1
    @17
    @6
    @2
    clt
    wbr
    #
    @24
    @1
    @17
    @25
    @24
    w3a
    cA
    ellogrn
    biimpi
    #
    simp3d
    @17
    @2
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @24
    @22
    wi
    cA
    imcl
    #
    pire
    @27
    @28
    wa
    @24
    @22
    @2
    cpi
    leneg
    biimpd
    sylancl
    sylc
    @17
    @22
    @23
    @17
    @6
    @7
    @6
    cr
    wcel
    @17
    cpi
    pire
    renegcli
    a1i
    @17
    @2
    @29
    renegcld
    #
    leloed
    biimpd
    sylc
    orcomd
    orcanai
    @10
    @7
    cpi
    clt
    wbr
    #
    @21
    @1
    @31
    @9
    @1
    @17
    @25
    @31
    @18
    @1
    @17
    @25
    @24
    @26
    simp2d
    @17
    @28
    @27
    @25
    @31
    wi
    pire
    @29
    @28
    @27
    wa
    @25
    @31
    cpi
    @2
    ltnegcon1
    biimpd
    sylancr
    sylc
    adantr
    @1
    @31
    @21
    wi
    #
    @9
    @1
    @17
    @32
    @18
    @17
    @7
    cr
    wcel
    @28
    @32
    @30
    pire
    @7
    cpi
    ltle
    sylancl
    syl
    adantr
    mpd
    @10
    @13
    @20
    @14
    @21
    @10
    @17
    @13
    @20
    wb
    @19
    @17
    @12
    @7
    @6
    clt
    cA
    imneg
    #
    breq2d
    syl
    @10
    @17
    @14
    @21
    wb
    @19
    @17
    @12
    @7
    cpi
    cle
    @33
    breq1d
    syl
    anbi12d
    mpbir2and
    @11
    @13
    @14
    3anass
    sylanbrc
    @4
    ellogrn
    sylibr
    ex
    orrd
    @1
    @8
    @3
    @5
    @1
    cpi
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    wa
    #
    @8
    @3
    wb
    @1
    @17
    @36
    @18
    @17
    @28
    @27
    @36
    pire
    @29
    @28
    @34
    @27
    @35
    cpi
    recn
    @2
    recn
    anim12i
    sylancr
    syl
    @36
    @8
    cpi
    @2
    wceq
    @3
    cpi
    @2
    neg11
    cpi
    @2
    eqcom
    syl6bb
    syl
    orbi1d
    mpbid
    orcanai
end
