include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "cz.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgcd.mm"
include "co.mm"
include "cle.mm"
include "wi.mm"
include "nnz.mm"
include "3anim123i.mm"
include "nnne0.mm"
include "neneqd.mm"
include "3ad2ant2.mm"
include "intnanrd.mm"
include "dvdslegcd.mm"
include "syl2anc.mm"

theorem nndvdslegcd
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. NN /\ M e. NN /\ N e. NN ) -> ( ( K || M /\ K || N ) -> K <_ ( M gcd N ) ) )

  proof
    cK
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    cN
    cn
    wcel
    #
    w3a
    #
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    wn
    cK
    cM
    cdvds
    wbr
    cK
    cN
    cdvds
    wbr
    wa
    cK
    cM
    cN
    cgcd
    co
    cle
    wbr
    wi
    @0
    @4
    @1
    @5
    @2
    @6
    cK
    nnz
    cM
    nnz
    cN
    nnz
    3anim123i
    @3
    @7
    @8
    @1
    @0
    @7
    wn
    @2
    @1
    cM
    cc0
    cM
    nnne0
    neneqd
    3ad2ant2
    intnanrd
    cK
    cM
    cN
    dvdslegcd
    syl2anc
end
