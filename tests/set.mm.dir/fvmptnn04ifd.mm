include "clt.mm"
include "wbr.mm"
include "csb.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "3ad2ant1.mm"
include "cn0.mm"
include "simp3.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wn.mm"
include "0red.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltnsymd.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "notbid.mm"
include "adantl.mm"
include "mpbird.mm"
include "pm2.21d.mm"
include "impancom.mm"
include "3adant3.mm"
include "imp.mm"
include "cr.mm"
include "nn0red.mm"
include "ltnsym.mm"
include "syl2anc.mm"
include "a1d.mm"
include "3imp.mm"
include "lttri3d.mm"
include "simplbda.mm"
include "eqidd.mm"
include "fvmptnn04if.mm"

theorem fvmptnn04ifd
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
  assert |- ( ( ph /\ S < N /\ [_ N / n ]_ D e. V ) -> ( G ` N ) = [_ N / n ]_ D )

  proof
    wph
    cS
    cN
    clt
    wbr
    #
    vn
    cN
    cD
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
    wph
    @0
    @4
    @5
    wi
    @2
    wph
    @4
    @0
    @5
    wph
    @4
    wa
    #
    @0
    @5
    @6
    @0
    wn
    #
    cS
    cc0
    clt
    wbr
    #
    wn
    #
    wph
    @9
    @4
    wph
    cc0
    cS
    wph
    0red
    wph
    cS
    fvmptnn04if.s
    nnred
    #
    wph
    cS
    fvmptnn04if.s
    nngt0d
    ltnsymd
    adantr
    @4
    @7
    @9
    wb
    wph
    @4
    @0
    @8
    cN
    cc0
    cS
    clt
    breq2
    notbid
    adantl
    mpbird
    pm2.21d
    impancom
    3adant3
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
    @11
    @3
    @12
    @13
    wph
    @0
    @12
    wn
    #
    @2
    wph
    @0
    @14
    wph
    cS
    cr
    wcel
    cN
    cr
    wcel
    @0
    @14
    wi
    @10
    wph
    cN
    fvmptnn04if.n
    nn0red
    #
    cS
    cN
    ltnsym
    syl2anc
    imp
    3adant3
    pm2.21d
    a1d
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
    wph
    @0
    @16
    @17
    wi
    @2
    wph
    @16
    @0
    @17
    wph
    @16
    wa
    @0
    @17
    wph
    @16
    @14
    @7
    wph
    cN
    cS
    @15
    @10
    lttri3d
    simplbda
    pm2.21d
    impancom
    3adant3
    imp
    @3
    @0
    wa
    @1
    eqidd
    fvmptnn04if
end
