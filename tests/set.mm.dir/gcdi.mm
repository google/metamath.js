include "cgcd.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "nn0mulcli.mm"
include "nn0cni.mm"
include "addcomli.mm"
include "oveq2i.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "nn0zi.mm"
include "gcdaddm.mm"
include "mp3an.mm"
include "cn0.mm"
include "numcl.mm"
include "eqeltrri.mm"
include "gcdcom.mm"
include "mp2an.mm"
include "3eqtr4i.mm"
include "eqtr3i.mm"

theorem gcdi
  let cR: class R
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  assume gcdi.1: |- K e. NN0
  assume gcdi.2: |- R e. NN0
  assume gcdi.3: |- N e. NN0
  assume gcdi.5: |- ( N gcd R ) = G
  assume gcdi.4: |- ( ( K x. N ) + R ) = M


  assert |- ( M gcd N ) = G

  proof
    cN
    cR
    cgcd
    co
    #
    cM
    cN
    cgcd
    co
    #
    cG
    cN
    cR
    cK
    cN
    cmul
    co
    #
    caddc
    co
    #
    cgcd
    co
    #
    cN
    cM
    cgcd
    co
    #
    @0
    @1
    @3
    cM
    cN
    cgcd
    @2
    cR
    cM
    @2
    cK
    cN
    gcdi.1
    gcdi.3
    nn0mulcli
    nn0cni
    cR
    gcdi.2
    nn0cni
    gcdi.4
    addcomli
    oveq2i
    cK
    cz
    wcel
    cN
    cz
    wcel
    #
    cR
    cz
    wcel
    @0
    @4
    wceq
    cK
    gcdi.1
    nn0zi
    cN
    gcdi.3
    nn0zi
    #
    cR
    gcdi.2
    nn0zi
    cK
    cN
    cR
    gcdaddm
    mp3an
    cM
    cz
    wcel
    @6
    @1
    @5
    wceq
    cM
    @2
    cR
    caddc
    co
    cM
    cn0
    gcdi.4
    cN
    cR
    cK
    gcdi.1
    gcdi.3
    gcdi.2
    numcl
    eqeltrri
    nn0zi
    @7
    cM
    cN
    gcdcom
    mp2an
    3eqtr4i
    gcdi.5
    eqtr3i
end
