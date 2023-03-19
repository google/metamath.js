include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cgrp.mm"
include "cbs.mm"
include "c6.mm"
include "clt.mm"
include "cabl.mm"
include "symggrp.mm"
include "adantr.mm"
include "cfa.mm"
include "cfn.mm"
include "wceq.mm"
include "cn0.mm"
include "2nn0.mm"
include "hashbnd.mm"
include "mp3an2.mm"
include "eqid.mm"
include "symghash.mm"
include "syl.mm"
include "cexp.mm"
include "co.mm"
include "cn.mm"
include "hashcl.mm"
include "faccl.mm"
include "nnred.mm"
include "nn0expcld.mm"
include "nn0red.mm"
include "cr.mm"
include "6re.mm"
include "a1i.mm"
include "facubnd.mm"
include "exple2lt6.mm"
include "sylancom.mm"
include "lelttrd.mm"
include "eqbrtrd.mm"
include "lt6abl.mm"
include "syl2anc.mm"

theorem pgrple2abl
  let cA: class A
  let cG: class G
  let cV: class V
  let vk: setvar k
  let vx: setvar x
  assume pgrple2abl.g: |- G = ( SymGrp ` A )


  assert |- ( ( A e. V /\ ( # ` A ) <_ 2 ) -> G e. Abel )

  proof
    cA
    cV
    wcel
    #
    cA
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    wa
    #
    cG
    cgrp
    wcel
    #
    cG
    cbs
    cfv
    #
    chash
    cfv
    #
    c6
    clt
    wbr
    cG
    cabl
    wcel
    @0
    @4
    @2
    cA
    cG
    cV
    pgrple2abl.g
    symggrp
    adantr
    @3
    @6
    @1
    cfa
    cfv
    #
    c6
    clt
    @3
    cA
    cfn
    wcel
    #
    @6
    @7
    wceq
    @0
    c2
    cn0
    wcel
    @2
    @8
    2nn0
    cA
    c2
    cV
    hashbnd
    mp3an2
    #
    cA
    @5
    cG
    pgrple2abl.g
    @5
    eqid
    #
    symghash
    syl
    @3
    @7
    @1
    @1
    cexp
    co
    #
    c6
    @3
    @7
    @3
    @1
    cn0
    wcel
    #
    @7
    cn
    wcel
    @3
    @8
    @12
    @9
    cA
    hashcl
    syl
    #
    @1
    faccl
    syl
    nnred
    @3
    @11
    @3
    @1
    @1
    @13
    @13
    nn0expcld
    nn0red
    c6
    cr
    wcel
    @3
    6re
    a1i
    @3
    @12
    @7
    @11
    cle
    wbr
    @13
    @1
    facubnd
    syl
    @0
    @2
    @12
    @11
    c6
    clt
    wbr
    @13
    @1
    exple2lt6
    sylancom
    lelttrd
    eqbrtrd
    @5
    cG
    @10
    lt6abl
    syl2anc
end
