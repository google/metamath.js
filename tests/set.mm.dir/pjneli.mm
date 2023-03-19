include "cno.mm"
include "cfv.mm"
include "cpjh.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "clt.mm"
include "pjnormi.mm"
include "biantrur.mm"
include "cort.mm"
include "c0v.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "pjoc1i.mm"
include "caddc.mm"
include "cc0.mm"
include "pjpythi.mm"
include "sq0.mm"
include "oveq2i.mm"
include "pjhclii.mm"
include "normcli.mm"
include "resqcli.mm"
include "recni.mm"
include "addid1i.mm"
include "eqtr2i.mm"
include "eqeq12i.mm"
include "choccli.mm"
include "0cn.mm"
include "sqcli.mm"
include "addcani.mm"
include "wb.mm"
include "chil.mm"
include "normge0.mm"
include "ax-mp.mm"
include "0le0.mm"
include "0re.mm"
include "sq11i.mm"
include "mp2an.mm"
include "norm-i-i.mm"
include "3bitri.mm"
include "bitr2i.mm"
include "necon3bbii.mm"
include "ltleni.mm"
include "3bitr4i.mm"

theorem pjneli
  let cA: class A
  let cH: class H
  assume pjnorm.1: |- H e. CH
  assume pjnorm.2: |- A e. ~H


  assert |- ( -. A e. H <-> ( normh ` ( ( projh ` H ) ` A ) ) < ( normh ` A ) )

  proof
    cA
    cno
    cfv
    #
    cA
    cH
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    wne
    #
    @2
    @0
    cle
    wbr
    #
    @3
    wa
    cA
    cH
    wcel
    #
    wn
    @2
    @0
    clt
    wbr
    @4
    @3
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjnormi
    biantrur
    @5
    @0
    @2
    @5
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    cfv
    #
    c0v
    wceq
    #
    @0
    c2
    cexp
    co
    #
    @2
    c2
    cexp
    co
    #
    wceq
    #
    @0
    @2
    wceq
    #
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjoc1i
    @11
    @10
    @7
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    @10
    cc0
    c2
    cexp
    co
    #
    caddc
    co
    #
    wceq
    #
    @8
    @9
    @15
    @10
    @17
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjpythi
    @17
    @10
    cc0
    caddc
    co
    @10
    @16
    cc0
    @10
    caddc
    sq0
    oveq2i
    @10
    @10
    @2
    @1
    cA
    cH
    pjnorm.1
    pjnorm.2
    pjhclii
    #
    normcli
    #
    resqcli
    recni
    #
    addid1i
    eqtr2i
    eqeq12i
    @18
    @14
    @16
    wceq
    #
    @13
    cc0
    wceq
    #
    @8
    @10
    @14
    @16
    @21
    @14
    @13
    @7
    cA
    @6
    cH
    pjnorm.1
    choccli
    pjnorm.2
    pjhclii
    #
    normcli
    #
    resqcli
    recni
    cc0
    0cn
    sqcli
    addcani
    cc0
    @13
    cle
    wbr
    #
    cc0
    cc0
    cle
    wbr
    @22
    @23
    wb
    @7
    chil
    wcel
    @26
    @24
    @7
    normge0
    ax-mp
    0le0
    @13
    cc0
    @25
    0re
    sq11i
    mp2an
    @7
    @24
    norm-i-i
    3bitri
    bitr2i
    cc0
    @0
    cle
    wbr
    #
    cc0
    @2
    cle
    wbr
    #
    @11
    @12
    wb
    cA
    chil
    wcel
    @27
    pjnorm.2
    cA
    normge0
    ax-mp
    @1
    chil
    wcel
    @28
    @19
    @1
    normge0
    ax-mp
    @0
    @2
    cA
    pjnorm.2
    normcli
    #
    @20
    sq11i
    mp2an
    3bitri
    necon3bbii
    @2
    @0
    @20
    @29
    ltleni
    3bitr4i
end
