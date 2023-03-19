include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cin.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "cdif.mm"
include "cun.mm"
include "wceq.mm"
include "c0.mm"
include "diffi.mm"
include "adantl.mm"
include "wss.mm"
include "simpl.mm"
include "inss1.mm"
include "ssfi.mm"
include "sylancl.mm"
include "sslin.mm"
include "ax-mp.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "sseq0.mm"
include "mp2an.mm"
include "a1i.mm"
include "hashun.mm"
include "syl3anc.mm"
include "uneq2i.mm"
include "uncom.mm"
include "inundif.mm"
include "3eqtri.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0cnd.mm"
include "syl.mm"
include "subadd2d.mm"
include "mpbird.mm"
include "oveq2d.mm"
include "adantr.mm"
include "addsubassd.mm"
include "undif2.mm"
include "fveq2i.mm"
include "syl5eqr.mm"
include "3eqtr4rd.mm"

theorem hashun3
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( # ` ( A u. B ) ) = ( ( ( # ` A ) + ( # ` B ) ) - ( # ` ( A i^i B ) ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    cA
    cB
    cin
    #
    chash
    cfv
    #
    cmin
    co
    #
    caddc
    co
    @3
    cB
    cA
    cdif
    #
    chash
    cfv
    #
    caddc
    co
    #
    @3
    @4
    caddc
    co
    @6
    cmin
    co
    cA
    cB
    cun
    #
    chash
    cfv
    #
    @2
    @7
    @9
    @3
    caddc
    @2
    @7
    @9
    wceq
    @9
    @6
    caddc
    co
    #
    @4
    wceq
    @2
    @8
    @5
    cun
    #
    chash
    cfv
    #
    @13
    @4
    @2
    @8
    cfn
    wcel
    #
    @5
    cfn
    wcel
    #
    @8
    @5
    cin
    #
    c0
    wceq
    #
    @15
    @13
    wceq
    @1
    @16
    @0
    cB
    cA
    diffi
    adantl
    #
    @2
    @0
    @5
    cA
    wss
    #
    @17
    @0
    @1
    simpl
    #
    cA
    cB
    inss1
    #
    cA
    @5
    ssfi
    sylancl
    #
    @19
    @2
    @18
    @8
    cA
    cin
    #
    wss
    #
    @25
    c0
    wceq
    @19
    @21
    @26
    @23
    @5
    cA
    @8
    sslin
    ax-mp
    @25
    cA
    @8
    cin
    #
    c0
    @8
    cA
    incom
    cA
    cB
    disjdif
    #
    eqtri
    @18
    @25
    sseq0
    mp2an
    a1i
    @8
    @5
    hashun
    syl3anc
    @2
    @14
    cB
    chash
    @14
    cB
    wceq
    @2
    @14
    @8
    cB
    cA
    cin
    #
    cun
    @29
    @8
    cun
    cB
    @5
    @29
    @8
    cA
    cB
    incom
    uneq2i
    @8
    @29
    uncom
    cB
    cA
    inundif
    3eqtri
    a1i
    fveq2d
    eqtr3d
    @2
    @4
    @6
    @9
    @2
    @4
    @1
    @4
    cn0
    wcel
    @0
    cB
    hashcl
    adantl
    nn0cnd
    #
    @2
    @6
    @2
    @17
    @6
    cn0
    wcel
    @24
    @5
    hashcl
    syl
    nn0cnd
    #
    @2
    @9
    @2
    @16
    @9
    cn0
    wcel
    @20
    @8
    hashcl
    syl
    nn0cnd
    subadd2d
    mpbird
    oveq2d
    @2
    @3
    @4
    @6
    @2
    @3
    @0
    @3
    cn0
    wcel
    @1
    cA
    hashcl
    adantr
    nn0cnd
    @30
    @31
    addsubassd
    @2
    @12
    cA
    @8
    cun
    #
    chash
    cfv
    #
    @10
    @32
    @11
    chash
    cA
    cB
    undif2
    fveq2i
    @2
    @0
    @16
    @27
    c0
    wceq
    #
    @33
    @10
    wceq
    @22
    @20
    @34
    @2
    @28
    a1i
    cA
    @8
    hashun
    syl3anc
    syl5eqr
    3eqtr4rd
end
