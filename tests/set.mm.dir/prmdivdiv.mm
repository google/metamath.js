include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wa.mm"
include "cc0.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "cmo.mm"
include "wceq.mm"
include "caddc.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "cz.mm"
include "wss.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "simpr.mm"
include "sseldi.mm"
include "wn.mm"
include "simpl.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnzd.mm"
include "prmnn.mm"
include "fzm1ndvds.mm"
include "sylan.mm"
include "prmdiv.mm"
include "syl3anc.mm"
include "simprd.mm"
include "nncnd.mm"
include "simpld.mm"
include "syl.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "breqtrd.mm"
include "wb.mm"
include "elfzelz.mm"
include "adantr.mm"
include "syl2anc.mm"
include "eqid.mm"
include "prmdiveq.mm"
include "mpbi2and.mm"

theorem prmdivdiv
  let cA: class A
  let cP: class P
  let cR: class R
  assume prmdiv.1: |- R = ( ( A ^ ( P - 2 ) ) mod P )


  assert |- ( ( P e. Prime /\ A e. ( 1 ... ( P - 1 ) ) ) -> A = ( ( R ^ ( P - 2 ) ) mod P ) )

  proof
    cP
    cprime
    wcel
    #
    cA
    c1
    cP
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cA
    cc0
    @1
    cfz
    co
    #
    wcel
    #
    cP
    cR
    cA
    cmul
    co
    #
    c1
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    cR
    cP
    c2
    cmin
    co
    cexp
    co
    cP
    cmo
    co
    #
    wceq
    #
    @4
    @2
    @5
    cA
    @2
    cc0
    c1
    caddc
    co
    #
    @1
    cfz
    co
    #
    @5
    c1
    @12
    @1
    cfz
    1e0p1
    oveq1i
    cc0
    cz
    wcel
    @13
    @5
    wss
    0z
    cc0
    @1
    fzp1ss
    ax-mp
    eqsstri
    @0
    @3
    simpr
    sseldi
    @4
    cP
    cA
    cR
    cmul
    co
    #
    c1
    cmin
    co
    #
    @8
    cdvds
    @4
    cR
    @2
    wcel
    #
    cP
    @15
    cdvds
    wbr
    #
    @4
    @0
    cA
    cz
    wcel
    cP
    cA
    cdvds
    wbr
    wn
    #
    @16
    @17
    wa
    @0
    @3
    simpl
    #
    @4
    cA
    @3
    cA
    cn
    wcel
    @0
    cA
    @1
    elfznn
    adantl
    #
    nnzd
    @0
    cP
    cn
    wcel
    #
    @3
    @18
    cP
    prmnn
    #
    cP
    cA
    fzm1ndvds
    sylan
    cA
    cP
    cR
    prmdiv.1
    prmdiv
    syl3anc
    #
    simprd
    @4
    @14
    @7
    c1
    cmin
    @4
    cA
    cR
    @4
    cA
    @20
    nncnd
    @4
    cR
    @4
    @16
    cR
    cn
    wcel
    @4
    @16
    @17
    @23
    simpld
    #
    cR
    @1
    elfznn
    syl
    nncnd
    mulcomd
    oveq1d
    breqtrd
    @4
    @0
    cR
    cz
    wcel
    #
    cP
    cR
    cdvds
    wbr
    wn
    #
    @6
    @9
    wa
    @11
    wb
    @19
    @4
    @16
    @25
    @24
    cR
    c1
    @1
    elfzelz
    syl
    @4
    @21
    @16
    @26
    @0
    @21
    @3
    @22
    adantr
    @24
    cP
    cR
    fzm1ndvds
    syl2anc
    cR
    cP
    @10
    cA
    @10
    eqid
    prmdiveq
    syl3anc
    mpbi2and
end
