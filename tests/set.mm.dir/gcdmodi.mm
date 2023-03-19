include "cgcd.mm"
include "co.mm"
include "cmo.mm"
include "oveq1i.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wceq.mm"
include "nn0zi.mm"
include "modgcd.mm"
include "mp2an.mm"
include "3eqtr3i.mm"
include "nnzi.mm"
include "gcdcom.mm"
include "3eqtri.mm"

theorem gcdmodi
  let cR: class R
  let cG: class G
  let cK: class K
  let cN: class N
  assume gcdi.1: |- K e. NN0
  assume gcdi.2: |- R e. NN0
  assume gcdmodi.3: |- N e. NN
  assume gcdmodi.4: |- ( K mod N ) = ( R mod N )
  assume gcdmodi.5: |- ( N gcd R ) = G


  assert |- ( K gcd N ) = G

  proof
    cK
    cN
    cgcd
    co
    #
    cR
    cN
    cgcd
    co
    #
    cN
    cR
    cgcd
    co
    #
    cG
    cK
    cN
    cmo
    co
    #
    cN
    cgcd
    co
    #
    cR
    cN
    cmo
    co
    #
    cN
    cgcd
    co
    #
    @0
    @1
    @3
    @5
    cN
    cgcd
    gcdmodi.4
    oveq1i
    cK
    cz
    wcel
    cN
    cn
    wcel
    #
    @4
    @0
    wceq
    cK
    gcdi.1
    nn0zi
    gcdmodi.3
    cK
    cN
    modgcd
    mp2an
    cR
    cz
    wcel
    #
    @7
    @6
    @1
    wceq
    cR
    gcdi.2
    nn0zi
    #
    gcdmodi.3
    cR
    cN
    modgcd
    mp2an
    3eqtr3i
    @8
    cN
    cz
    wcel
    @1
    @2
    wceq
    @9
    cN
    gcdmodi.3
    nnzi
    cR
    cN
    gcdcom
    mp2an
    gcdmodi.5
    3eqtri
end
