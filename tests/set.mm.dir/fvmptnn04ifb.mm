include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "csb.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "3ad2ant1.mm"
include "cn0.mm"
include "simp3.mm"
include "wceq.mm"
include "wne.mm"
include "wi.mm"
include "cr.mm"
include "cle.mm"
include "wb.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "jca.mm"
include "ne0gt0.mm"
include "3syl.mm"
include "biimprcd.mm"
include "adantr.mm"
include "impcom.mm"
include "3adant3.mm"
include "wn.mm"
include "df-ne.mm"
include "biimpi.mm"
include "pm2.21d.mm"
include "syl.mm"
include "imp.mm"
include "eqidd.mm"
include "simpr.mm"
include "ltned.mm"
include "neneqd.mm"
include "adantrl.mm"
include "nnred.mm"
include "ltnsym.mm"
include "syl2anc.mm"
include "com12.mm"
include "adantl.mm"
include "fvmptnn04if.mm"

theorem fvmptnn04ifb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cG: class G
  let cN: class N
  let cV: class V
  assume fvmptnn04if.g: |- G = ( n e. NN0 |-> if ( n = 0 , A , if ( n = S , C , if ( S < n , D , B ) ) ) )
  assume fvmptnn04if.s: |- ( ph -> S e. NN )
  assume fvmptnn04if.n: |- ( ph -> N e. NN0 )

  disjoint N n
  disjoint S n
  disjoint A n
  disjoint V n
  assert |- ( ( ph /\ ( 0 < N /\ N < S ) /\ [_ N / n ]_ B e. V ) -> ( G ` N ) = [_ N / n ]_ B )

  proof
    wph
    cc0
    cN
    clt
    wbr
    #
    cN
    cS
    clt
    wbr
    #
    wa
    #
    vn
    cN
    cB
    csb
    #
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cD
    cS
    vn
    cG
    cN
    cV
    @3
    fvmptnn04if.g
    wph
    @2
    cS
    cn
    wcel
    @4
    fvmptnn04if.s
    3ad2ant1
    wph
    @2
    cN
    cn0
    wcel
    #
    @4
    fvmptnn04if.n
    3ad2ant1
    wph
    @2
    @4
    simp3
    @5
    cN
    cc0
    wceq
    #
    @3
    vn
    cN
    cA
    csb
    wceq
    #
    @5
    cN
    cc0
    wne
    #
    @7
    @8
    wi
    wph
    @2
    @9
    @4
    @2
    wph
    @9
    @0
    wph
    @9
    wi
    @1
    wph
    @9
    @0
    wph
    @6
    cN
    cr
    wcel
    #
    cc0
    cN
    cle
    wbr
    #
    wa
    @9
    @0
    wb
    fvmptnn04if.n
    @6
    @10
    @11
    cN
    nn0re
    #
    cN
    nn0ge0
    jca
    cN
    ne0gt0
    3syl
    biimprcd
    adantr
    impcom
    3adant3
    @9
    @7
    @8
    @9
    @7
    wn
    cN
    cc0
    df-ne
    biimpi
    pm2.21d
    syl
    imp
    @5
    @0
    @1
    w3a
    @3
    eqidd
    @5
    cN
    cS
    wceq
    #
    @3
    vn
    cN
    cC
    csb
    wceq
    #
    @5
    @13
    @14
    wph
    @2
    @13
    wn
    #
    @4
    wph
    @1
    @15
    @0
    wph
    @1
    wa
    #
    cN
    cS
    @16
    cN
    cS
    wph
    @10
    @1
    wph
    @6
    @10
    fvmptnn04if.n
    @12
    syl
    #
    adantr
    wph
    @1
    simpr
    ltned
    neneqd
    adantrl
    3adant3
    pm2.21d
    imp
    @5
    cS
    cN
    clt
    wbr
    #
    @3
    vn
    cN
    cD
    csb
    wceq
    #
    @5
    @18
    @19
    wph
    @2
    @18
    wn
    #
    @4
    @2
    wph
    @20
    @1
    wph
    @20
    wi
    @0
    wph
    @1
    @20
    wph
    @10
    cS
    cr
    wcel
    @1
    @20
    wi
    @17
    wph
    cS
    fvmptnn04if.s
    nnred
    cN
    cS
    ltnsym
    syl2anc
    com12
    adantl
    impcom
    3adant3
    pm2.21d
    imp
    fvmptnn04if
end
