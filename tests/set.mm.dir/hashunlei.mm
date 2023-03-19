include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cun.mm"
include "simpli.mm"
include "unfi.mm"
include "mp2an.mm"
include "eqeltri.mm"
include "caddc.mm"
include "co.mm"
include "fveq2i.mm"
include "hashun2.mm"
include "eqbrtri.mm"
include "simpri.mm"
include "cn0.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0rei.mm"
include "le2addi.mm"
include "breqtri.mm"
include "readdcli.mm"
include "cr.mm"
include "eqeltrri.mm"
include "letri.mm"
include "pm3.2i.mm"

theorem hashunlei
  let cA: class A
  let cB: class B
  let cC: class C
  let cK: class K
  let cM: class M
  let cN: class N
  assume hashunlei.c: |- C = ( A u. B )
  assume hashunlei.a: |- ( A e. Fin /\ ( # ` A ) <_ K )
  assume hashunlei.b: |- ( B e. Fin /\ ( # ` B ) <_ M )
  assume hashunlei.k: |- K e. NN0
  assume hashunlei.m: |- M e. NN0
  assume hashunlei.n: |- ( K + M ) = N


  assert |- ( C e. Fin /\ ( # ` C ) <_ N )

  proof
    cC
    cfn
    wcel
    #
    cC
    chash
    cfv
    #
    cN
    cle
    wbr
    #
    cC
    cA
    cB
    cun
    #
    cfn
    hashunlei.c
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    @3
    cfn
    wcel
    @4
    cA
    chash
    cfv
    #
    cK
    cle
    wbr
    #
    hashunlei.a
    simpli
    #
    @5
    cB
    chash
    cfv
    #
    cM
    cle
    wbr
    #
    hashunlei.b
    simpli
    #
    cA
    cB
    unfi
    mp2an
    eqeltri
    #
    @1
    @6
    @9
    caddc
    co
    #
    cle
    wbr
    @13
    cN
    cle
    wbr
    @2
    @1
    @3
    chash
    cfv
    #
    @13
    cle
    cC
    @3
    chash
    hashunlei.c
    fveq2i
    @4
    @5
    @14
    @13
    cle
    wbr
    @8
    @11
    cA
    cB
    hashun2
    mp2an
    eqbrtri
    @13
    cK
    cM
    caddc
    co
    #
    cN
    cle
    @7
    @10
    @13
    @15
    cle
    wbr
    @4
    @7
    hashunlei.a
    simpri
    @5
    @10
    hashunlei.b
    simpri
    @6
    @9
    cK
    cM
    @6
    @4
    @6
    cn0
    wcel
    @8
    cA
    hashcl
    ax-mp
    nn0rei
    #
    @9
    @5
    @9
    cn0
    wcel
    @11
    cB
    hashcl
    ax-mp
    nn0rei
    #
    cK
    hashunlei.k
    nn0rei
    #
    cM
    hashunlei.m
    nn0rei
    #
    le2addi
    mp2an
    hashunlei.n
    breqtri
    @1
    @13
    cN
    @1
    @0
    @1
    cn0
    wcel
    @12
    cC
    hashcl
    ax-mp
    nn0rei
    @6
    @9
    @16
    @17
    readdcli
    @15
    cN
    cr
    hashunlei.n
    cK
    cM
    @18
    @19
    readdcli
    eqeltrri
    letri
    mp2an
    pm3.2i
end
