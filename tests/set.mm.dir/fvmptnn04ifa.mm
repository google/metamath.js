include "cc0.mm"
include "wceq.mm"
include "csb.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "3ad2ant1.mm"
include "cn0.mm"
include "simp3.mm"
include "wa.mm"
include "eqidd.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "simpr.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "pm2.21d.mm"
include "impancom.mm"
include "3adant3.mm"
include "3imp.mm"
include "wne.mm"
include "nnne0d.mm"
include "necomd.mm"
include "adantr.mm"
include "wb.mm"
include "neeq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "imp.mm"
include "wn.mm"
include "nnnn0.mm"
include "nn0nlt0.mm"
include "3syl.mm"
include "breq2.mm"
include "notbid.mm"
include "fvmptnn04if.mm"

theorem fvmptnn04ifa
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
  assert |- ( ( ph /\ N = 0 /\ [_ N / n ]_ A e. V ) -> ( G ` N ) = [_ N / n ]_ A )

  proof
    wph
    cN
    cc0
    wceq
    #
    vn
    cN
    cA
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
    @1
    fvmptnn04if.g
    wph
    @0
    cS
    cn
    wcel
    #
    @2
    fvmptnn04if.s
    3ad2ant1
    wph
    @0
    cN
    cn0
    wcel
    @2
    fvmptnn04if.n
    3ad2ant1
    wph
    @0
    @2
    simp3
    @3
    @0
    wa
    @1
    eqidd
    @3
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
    @1
    vn
    cN
    cB
    csb
    wceq
    #
    wph
    @0
    @5
    @6
    @7
    wi
    #
    wi
    @2
    wph
    @5
    @0
    @8
    wph
    @5
    wa
    #
    @0
    @8
    @9
    cN
    cc0
    @9
    cN
    wph
    @5
    simpr
    gt0ne0d
    neneqd
    pm2.21d
    impancom
    3adant3
    3imp
    @3
    cN
    cS
    wceq
    #
    @1
    vn
    cN
    cC
    csb
    wceq
    #
    @3
    @10
    @11
    @3
    cN
    cS
    wph
    @0
    cN
    cS
    wne
    #
    @2
    wph
    @0
    wa
    #
    @12
    cc0
    cS
    wne
    #
    wph
    @14
    @0
    wph
    cS
    cc0
    wph
    cS
    fvmptnn04if.s
    nnne0d
    necomd
    adantr
    @0
    @12
    @14
    wb
    wph
    cN
    cc0
    cS
    neeq1
    adantl
    mpbird
    3adant3
    neneqd
    pm2.21d
    imp
    @3
    cS
    cN
    clt
    wbr
    #
    @1
    vn
    cN
    cD
    csb
    wceq
    #
    @3
    @15
    @16
    wph
    @0
    @15
    wn
    #
    @2
    @13
    @17
    cS
    cc0
    clt
    wbr
    #
    wn
    #
    wph
    @19
    @0
    wph
    @4
    cS
    cn0
    wcel
    @19
    fvmptnn04if.s
    cS
    nnnn0
    cS
    nn0nlt0
    3syl
    adantr
    @0
    @17
    @19
    wb
    wph
    @0
    @15
    @18
    cN
    cc0
    cS
    clt
    breq2
    notbid
    adantl
    mpbird
    3adant3
    pm2.21d
    imp
    fvmptnn04if
end
