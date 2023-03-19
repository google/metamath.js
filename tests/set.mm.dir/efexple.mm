include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cz.mm"
include "crp.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cle.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "ce.mm"
include "cdiv.mm"
include "cfl.mm"
include "wceq.mm"
include "simpl.mm"
include "cc0.mm"
include "0lt1.mm"
include "wi.mm"
include "0re.mm"
include "1re.mm"
include "lttr.mm"
include "mp3an12.mm"
include "mpani.mm"
include "imp.mm"
include "elrpd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "reexplog.mm"
include "syl2anc.mm"
include "reeflog.mm"
include "3ad2ant3.mm"
include "eqcomd.mm"
include "breq12d.mm"
include "wb.mm"
include "zre.mm"
include "3ad2ant2.mm"
include "rplogcl.mm"
include "rpred.mm"
include "remulcld.mm"
include "relogcl.mm"
include "efle.mm"
include "lemuldivd.mm"
include "rerpdivcld.mm"
include "flge.mm"
include "bitrd.mm"
include "3bitr2d.mm"

theorem efexple
  let cA: class A
  let cB: class B
  let cN: class N


  assert |- ( ( ( A e. RR /\ 1 < A ) /\ N e. ZZ /\ B e. RR+ ) -> ( ( A ^ N ) <_ B <-> N <_ ( |_ ` ( ( log ` B ) / ( log ` A ) ) ) ) )

  proof
    cA
    cr
    wcel
    #
    c1
    cA
    clt
    wbr
    #
    wa
    #
    cN
    cz
    wcel
    #
    cB
    crp
    wcel
    #
    w3a
    #
    cA
    cN
    cexp
    co
    #
    cB
    cle
    wbr
    cN
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cB
    clog
    cfv
    #
    ce
    cfv
    #
    cle
    wbr
    #
    @8
    @10
    cle
    wbr
    #
    cN
    @10
    @7
    cdiv
    co
    #
    cfl
    cfv
    cle
    wbr
    #
    @5
    @6
    @9
    cB
    @11
    cle
    @5
    cA
    crp
    wcel
    #
    @3
    @6
    @9
    wceq
    @2
    @3
    @16
    @4
    @2
    cA
    @0
    @1
    simpl
    @0
    @1
    cc0
    cA
    clt
    wbr
    #
    @0
    cc0
    c1
    clt
    wbr
    #
    @1
    @17
    0lt1
    cc0
    cr
    wcel
    c1
    cr
    wcel
    @0
    @18
    @1
    wa
    @17
    wi
    0re
    1re
    cc0
    c1
    cA
    lttr
    mp3an12
    mpani
    imp
    elrpd
    3ad2ant1
    @2
    @3
    @4
    simp2
    #
    cA
    cN
    reexplog
    syl2anc
    @5
    @11
    cB
    @4
    @2
    @11
    cB
    wceq
    @3
    cB
    reeflog
    3ad2ant3
    eqcomd
    breq12d
    @5
    @8
    cr
    wcel
    @10
    cr
    wcel
    #
    @13
    @12
    wb
    @5
    cN
    @7
    @3
    @2
    cN
    cr
    wcel
    @4
    cN
    zre
    3ad2ant2
    #
    @5
    @7
    @2
    @3
    @7
    crp
    wcel
    @4
    cA
    rplogcl
    3ad2ant1
    #
    rpred
    remulcld
    @4
    @2
    @20
    @3
    cB
    relogcl
    3ad2ant3
    #
    @8
    @10
    efle
    syl2anc
    @5
    @13
    cN
    @14
    cle
    wbr
    #
    @15
    @5
    cN
    @10
    @7
    @21
    @23
    @22
    lemuldivd
    @5
    @14
    cr
    wcel
    @3
    @24
    @15
    wb
    @5
    @10
    @7
    @23
    @22
    rerpdivcld
    @19
    @14
    cN
    flge
    syl2anc
    bitrd
    3bitr2d
end
