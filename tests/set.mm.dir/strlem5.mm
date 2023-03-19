include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cpjh.mm"
include "cch.mm"
include "strlem2.mm"
include "ax-mp.mm"
include "wn.mm"
include "eldif.mm"
include "chil.mm"
include "cheli.mm"
include "wb.mm"
include "pjnel.mm"
include "mpan.mm"
include "biimpa.mm"
include "sylan.mm"
include "sylbi.mm"
include "breq2.mm"
include "syl5ib.mm"
include "impcom.mm"
include "eldifi.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "pjhcli.mm"
include "normcl.mm"
include "syl.mm"
include "normge0.mm"
include "1re.mm"
include "0le1.mm"
include "lt2sq.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "3syl.mm"
include "adantr.mm"
include "mpbid.mm"
include "syl5eqbr.mm"
include "sq1.mm"
include "syl6breq.mm"

theorem strlem5
  let wph: wff ph
  let vx: setvar x
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  assume strlem3.1: |- S = ( x e. CH |-> ( ( normh ` ( ( projh ` x ) ` u ) ) ^ 2 ) )
  assume strlem3.2: |- ( ph <-> ( u e. ( A \ B ) /\ ( normh ` u ) = 1 ) )
  assume strlem3.3: |- A e. CH
  assume strlem3.4: |- B e. CH

  disjoint ph x
  disjoint u x
  disjoint A x
  disjoint B x
  assert |- ( ph -> ( S ` B ) < 1 )

  proof
    wph
    vu
    cv
    #
    cA
    cB
    cdif
    wcel
    #
    @0
    cno
    cfv
    #
    c1
    wceq
    #
    wa
    #
    cB
    cS
    cfv
    #
    c1
    clt
    wbr
    strlem3.2
    @4
    @5
    c1
    c2
    cexp
    co
    #
    c1
    clt
    @4
    @5
    @0
    cB
    cpjh
    cfv
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @6
    clt
    cB
    cch
    wcel
    #
    @5
    @9
    wceq
    strlem3.4
    vx
    vu
    cB
    cS
    strlem3.1
    strlem2
    ax-mp
    @4
    @8
    c1
    clt
    wbr
    #
    @9
    @6
    clt
    wbr
    #
    @3
    @1
    @11
    @1
    @8
    @2
    clt
    wbr
    #
    @3
    @11
    @1
    @0
    cA
    wcel
    #
    @0
    cB
    wcel
    wn
    #
    wa
    @13
    @0
    cA
    cB
    eldif
    @14
    @0
    chil
    wcel
    #
    @15
    @13
    @0
    cA
    strlem3.3
    cheli
    #
    @16
    @15
    @13
    @10
    @16
    @15
    @13
    wb
    strlem3.4
    @0
    cB
    pjnel
    mpan
    biimpa
    sylan
    sylbi
    @2
    c1
    @8
    clt
    breq2
    syl5ib
    impcom
    @1
    @11
    @12
    wb
    #
    @3
    @1
    @14
    @16
    @18
    @0
    cA
    cB
    eldifi
    @17
    @16
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    @18
    @16
    @7
    chil
    wcel
    #
    @19
    @0
    cB
    strlem3.4
    pjhcli
    #
    @7
    normcl
    syl
    @16
    @21
    @20
    @22
    @7
    normge0
    syl
    @19
    @20
    wa
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    @18
    1re
    0le1
    @8
    c1
    lt2sq
    mpanr12
    syl2anc
    3syl
    adantr
    mpbid
    syl5eqbr
    sq1
    syl6breq
    sylbi
end
