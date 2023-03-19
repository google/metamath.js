include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "simpli.mm"
include "ssfi.mm"
include "mp2an.mm"
include "cdom.mm"
include "ssdomg.mm"
include "mp2.mm"
include "wb.mm"
include "hashdom.mm"
include "mpbir.mm"
include "simpri.mm"
include "cn0.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0rei.mm"
include "letri.mm"
include "pm3.2i.mm"

theorem hashsslei
  let cA: class A
  let cB: class B
  let cN: class N
  assume hashsslei.b: |- B C_ A
  assume hashsslei.a: |- ( A e. Fin /\ ( # ` A ) <_ N )
  assume hashsslei.n: |- N e. NN0


  assert |- ( B e. Fin /\ ( # ` B ) <_ N )

  proof
    cB
    cfn
    wcel
    #
    cB
    chash
    cfv
    #
    cN
    cle
    wbr
    #
    cA
    cfn
    wcel
    #
    cB
    cA
    wss
    #
    @0
    @3
    cA
    chash
    cfv
    #
    cN
    cle
    wbr
    #
    hashsslei.a
    simpli
    #
    hashsslei.b
    cA
    cB
    ssfi
    mp2an
    #
    @1
    @5
    cle
    wbr
    #
    @6
    @2
    @9
    cB
    cA
    cdom
    wbr
    #
    @3
    @4
    @10
    @7
    hashsslei.b
    cB
    cA
    cfn
    ssdomg
    mp2
    @0
    @3
    @9
    @10
    wb
    @8
    @7
    cB
    cA
    cfn
    hashdom
    mp2an
    mpbir
    @3
    @6
    hashsslei.a
    simpri
    @1
    @5
    cN
    @1
    @0
    @1
    cn0
    wcel
    @8
    cB
    hashcl
    ax-mp
    nn0rei
    @5
    @3
    @5
    cn0
    wcel
    @7
    cA
    hashcl
    ax-mp
    nn0rei
    cN
    hashsslei.n
    nn0rei
    letri
    mp2an
    pm3.2i
end
