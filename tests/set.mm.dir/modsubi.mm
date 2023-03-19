include "cneg.mm"
include "caddc.mm"
include "co.mm"
include "cmo.mm"
include "cmin.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "crp.mm"
include "wceq.mm"
include "nnrei.mm"
include "nn0addcli.mm"
include "nn0rei.mm"
include "eqeltrri.mm"
include "pm3.2i.mm"
include "renegcli.mm"
include "cn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "modadd1.mm"
include "mp3an.mm"
include "nncni.mm"
include "nn0cni.mm"
include "negsubi.mm"
include "oveq1i.mm"
include "recni.mm"
include "subadd2i.mm"
include "mpbir.mm"
include "eqtri.mm"
include "3eqtr3i.mm"

theorem modsubi
  let cA: class A
  let cB: class B
  let cK: class K
  let cM: class M
  let cN: class N
  assume modsubi.1: |- N e. NN
  assume modsubi.2: |- A e. NN
  assume modsubi.3: |- B e. NN0
  assume modsubi.4: |- M e. NN0
  assume modsubi.6: |- ( A mod N ) = ( K mod N )
  assume modsubi.5: |- ( M + B ) = K


  assert |- ( ( A - B ) mod N ) = ( M mod N )

  proof
    cA
    cB
    cneg
    #
    caddc
    co
    #
    cN
    cmo
    co
    #
    cK
    @0
    caddc
    co
    #
    cN
    cmo
    co
    #
    cA
    cB
    cmin
    co
    #
    cN
    cmo
    co
    cM
    cN
    cmo
    co
    cA
    cr
    wcel
    #
    cK
    cr
    wcel
    #
    wa
    @0
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    wa
    cA
    cN
    cmo
    co
    cK
    cN
    cmo
    co
    wceq
    @2
    @4
    wceq
    @6
    @7
    cA
    modsubi.2
    nnrei
    cM
    cB
    caddc
    co
    #
    cK
    cr
    modsubi.5
    @10
    cM
    cB
    modsubi.4
    modsubi.3
    nn0addcli
    nn0rei
    eqeltrri
    #
    pm3.2i
    @8
    @9
    cB
    cB
    modsubi.3
    nn0rei
    renegcli
    cN
    cn
    wcel
    @9
    modsubi.1
    cN
    nnrp
    ax-mp
    pm3.2i
    modsubi.6
    cA
    cK
    @0
    cN
    modadd1
    mp3an
    @1
    @5
    cN
    cmo
    cA
    cB
    cA
    modsubi.2
    nncni
    cB
    modsubi.3
    nn0cni
    #
    negsubi
    oveq1i
    @3
    cM
    cN
    cmo
    @3
    cK
    cB
    cmin
    co
    #
    cM
    cK
    cB
    cK
    @11
    recni
    #
    @12
    negsubi
    @13
    cM
    wceq
    @10
    cK
    wceq
    modsubi.5
    cK
    cB
    cM
    @14
    @12
    cM
    modsubi.4
    nn0cni
    subadd2i
    mpbir
    eqtri
    oveq1i
    3eqtr3i
end
