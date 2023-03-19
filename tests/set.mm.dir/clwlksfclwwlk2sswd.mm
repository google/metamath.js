include "cv.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "chash.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "clwlksfclwwlk2wrd.mm"
include "clwlksfclwwlk1hash.mm"
include "wa.mm"
include "swrd0len.mm"
include "eqcomd.mm"
include "syl2anc.mm"

theorem clwlksfclwwlk2sswd
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  assert |- ( c e. C -> ( # ` A ) = ( # ` ( B substr <. 0 , ( # ` A ) >. ) ) )

  proof
    vc
    cv
    cC
    wcel
    cB
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cA
    chash
    cfv
    #
    cc0
    cB
    chash
    cfv
    cfz
    co
    wcel
    #
    @2
    cB
    cc0
    @2
    cop
    csubstr
    co
    chash
    cfv
    #
    wceq
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk2wrd
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hash
    @1
    @3
    wa
    @4
    @2
    @0
    cB
    @2
    swrd0len
    eqcomd
    syl2anc
end
