include "ccyg.mm"
include "wcel.mm"
include "cv.mm"
include "czn.mm"
include "cfv.mm"
include "cgic.mm"
include "wbr.mm"
include "cn0.mm"
include "wrex.mm"
include "cbs.mm"
include "cfn.mm"
include "chash.mm"
include "cc0.mm"
include "cif.mm"
include "hashcl.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "0nn0.mm"
include "a1i.mm"
include "ifclda.mm"
include "eqid.mm"
include "cygzn.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "gicsym.mm"
include "zncyg.mm"
include "giccyg.mm"
include "syl2imc.mm"
include "rexlimiv.mm"
include "impbii.mm"

theorem cygth
  let vn: setvar n
  let cG: class G

  disjoint G n
  assert |- ( G e. CycGrp <-> E. n e. NN0 G ~=g ( Z/nZ ` n ) )

  proof
    cG
    ccyg
    wcel
    #
    cG
    vn
    cv
    #
    czn
    cfv
    #
    cgic
    wbr
    #
    vn
    cn0
    wrex
    #
    @0
    cG
    cbs
    cfv
    #
    cfn
    wcel
    #
    @5
    chash
    cfv
    #
    cc0
    cif
    #
    cn0
    wcel
    cG
    @8
    czn
    cfv
    #
    cgic
    wbr
    #
    @4
    @0
    @6
    @7
    cc0
    cn0
    @6
    @7
    cn0
    wcel
    @0
    @5
    hashcl
    adantl
    cc0
    cn0
    wcel
    @0
    @6
    wn
    wa
    0nn0
    a1i
    ifclda
    @5
    cG
    @8
    @9
    @5
    eqid
    @8
    eqid
    @9
    eqid
    cygzn
    @3
    @10
    vn
    @8
    cn0
    @1
    @8
    wceq
    @2
    @9
    cG
    cgic
    @1
    @8
    czn
    fveq2
    breq2d
    rspcev
    syl2anc
    @3
    @0
    vn
    cn0
    @3
    @2
    cG
    cgic
    wbr
    @1
    cn0
    wcel
    @2
    ccyg
    wcel
    @0
    cG
    @2
    gicsym
    @1
    @2
    @2
    eqid
    zncyg
    @2
    cG
    giccyg
    syl2imc
    rexlimiv
    impbii
end
