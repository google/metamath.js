include "wceq.mm"
include "csb.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "3ad2ant1.mm"
include "cn0.mm"
include "simp3.mm"
include "cc0.mm"
include "wn.mm"
include "wa.mm"
include "nnne0.mm"
include "neneqd.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq1.mm"
include "notbid.mm"
include "adantl.mm"
include "mpbird.mm"
include "3adant3.mm"
include "pm2.21d.mm"
include "imp.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "nn0red.mm"
include "nnred.mm"
include "lttri3d.mm"
include "simprbda.mm"
include "a1d.mm"
include "3imp.mm"
include "eqidd.mm"
include "simplbda.mm"
include "fvmptnn04if.mm"

theorem fvmptnn04ifc
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
  assert |- ( ( ph /\ N = S /\ [_ N / n ]_ C e. V ) -> ( G ` N ) = [_ N / n ]_ C )

  proof
    wph
    cN
    cS
    wceq
    #
    vn
    cN
    cC
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
    cN
    cc0
    wceq
    #
    @1
    vn
    cN
    cA
    csb
    wceq
    #
    @3
    @5
    @6
    wph
    @0
    @5
    wn
    #
    @2
    wph
    @0
    wa
    #
    @7
    cS
    cc0
    wceq
    #
    wn
    #
    wph
    @10
    @0
    wph
    @4
    @10
    fvmptnn04if.s
    @4
    cS
    cc0
    cS
    nnne0
    neneqd
    syl
    adantr
    @0
    @7
    @10
    wb
    wph
    @0
    @5
    @9
    cN
    cS
    cc0
    eqeq1
    notbid
    adantl
    mpbird
    3adant3
    pm2.21d
    imp
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
    @3
    @12
    @13
    wi
    #
    @11
    wph
    @0
    @14
    @2
    @8
    @12
    @13
    wph
    @0
    @12
    wn
    #
    cS
    cN
    clt
    wbr
    #
    wn
    #
    wph
    cN
    cS
    wph
    cN
    fvmptnn04if.n
    nn0red
    wph
    cS
    fvmptnn04if.s
    nnred
    lttri3d
    #
    simprbda
    pm2.21d
    3adant3
    a1d
    3imp
    @3
    @0
    wa
    @1
    eqidd
    @3
    @16
    @1
    vn
    cN
    cD
    csb
    wceq
    #
    @3
    @16
    @19
    wph
    @0
    @17
    @2
    wph
    @0
    @15
    @17
    @18
    simplbda
    3adant3
    pm2.21d
    imp
    fvmptnn04if
end
