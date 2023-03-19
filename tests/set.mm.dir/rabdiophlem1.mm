include "cn0.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "cz.mm"
include "wss.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "zex.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "wf.mm"
include "mzpf.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "ssralv.mm"
include "mpsyl.mm"

theorem rabdiophlem1
  let vt: setvar t
  let cA: class A
  let cN: class N

  disjoint N t
  assert |- ( ( t e. ( ZZ ^m ( 1 ... N ) ) |-> A ) e. ( mzPoly ` ( 1 ... N ) ) -> A. t e. ( NN0 ^m ( 1 ... N ) ) A e. ZZ )

  proof
    cn0
    c1
    cN
    cfz
    co
    #
    cmap
    co
    #
    cz
    @0
    cmap
    co
    #
    wss
    #
    vt
    @2
    cA
    cmpt
    #
    @0
    cmzp
    cfv
    wcel
    #
    cA
    cz
    wcel
    #
    vt
    @2
    wral
    #
    @6
    vt
    @1
    wral
    cz
    cvv
    wcel
    cn0
    cz
    wss
    @3
    zex
    nn0ssz
    cn0
    cz
    @0
    cvv
    mapss
    mp2an
    @5
    @2
    cz
    @4
    wf
    @7
    @4
    @0
    mzpf
    vt
    @2
    cz
    cA
    @4
    @4
    eqid
    fmpt
    sylibr
    @6
    vt
    @1
    @2
    ssralv
    mpsyl
end
