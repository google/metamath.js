include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "csp.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cr.mm"
include "wa.mm"
include "hicl.mm"
include "abscld.mm"
include "3adant3.mm"
include "normcl.mm"
include "remulcl.mm"
include "syl2an.mm"
include "3ad2ant2.mm"
include "bcs.mm"
include "cc0.mm"
include "3ad2ant1.mm"
include "normge0.mm"
include "jca.mm"
include "simp3.mm"
include "1re.mm"
include "lemul1a.mm"
include "mp3anl2.mm"
include "syl21anc.mm"
include "wceq.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breqtrd.mm"
include "letrd.mm"

theorem bcs2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H /\ ( normh ` A ) <_ 1 ) -> ( abs ` ( A .ih B ) ) <_ ( normh ` B ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    w3a
    #
    cA
    cB
    csp
    co
    #
    cabs
    cfv
    #
    @2
    cB
    cno
    cfv
    #
    cmul
    co
    #
    @7
    @0
    @1
    @6
    cr
    wcel
    @3
    @0
    @1
    wa
    @5
    cA
    cB
    hicl
    abscld
    3adant3
    @0
    @1
    @8
    cr
    wcel
    #
    @3
    @0
    @2
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @9
    @1
    cA
    normcl
    #
    cB
    normcl
    #
    @2
    @7
    remulcl
    syl2an
    3adant3
    @1
    @0
    @11
    @3
    @13
    3ad2ant2
    #
    @0
    @1
    @6
    @8
    cle
    wbr
    @3
    cA
    cB
    bcs
    3adant3
    @4
    @8
    c1
    @7
    cmul
    co
    #
    @7
    cle
    @4
    @10
    @11
    cc0
    @7
    cle
    wbr
    #
    wa
    #
    @3
    @8
    @15
    cle
    wbr
    #
    @0
    @1
    @10
    @3
    @12
    3ad2ant1
    @4
    @11
    @16
    @14
    @1
    @0
    @16
    @3
    cB
    normge0
    3ad2ant2
    jca
    @0
    @1
    @3
    simp3
    @10
    c1
    cr
    wcel
    @17
    @3
    @18
    1re
    @2
    c1
    @7
    lemul1a
    mp3anl2
    syl21anc
    @1
    @0
    @15
    @7
    wceq
    @3
    @1
    @7
    @1
    @7
    @13
    recnd
    mulid2d
    3ad2ant2
    breqtrd
    letrd
end
