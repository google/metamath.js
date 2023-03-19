include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "crctcshwlk.mm"
include "cdm.mm"
include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "ccrcts.mm"
include "crctistrl.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wf1.mm"
include "trlf1.mm"
include "wf.mm"
include "df-f1.mm"
include "iswrdi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl.mm"
include "3syl.mm"
include "elfzoelz.mm"
include "df-3an.mm"
include "sylanbrc.mm"
include "cshinj.mm"
include "mpisyl.mm"
include "istrl.mm"

theorem crctcshtrl
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )
  assume crctcsh.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F x
  disjoint I x
  disjoint V x
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint G i
  disjoint G j
  disjoint H j
  disjoint I i
  disjoint I j
  disjoint I k
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint P i
  disjoint P j
  disjoint P k
  disjoint Q j
  disjoint S i
  disjoint S j
  disjoint S k
  disjoint V i
  disjoint V j
  disjoint V k
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> H ( Trails ` G ) Q )

  proof
    wph
    cH
    cQ
    cG
    cwlks
    cfv
    wbr
    cH
    ccnv
    wfun
    #
    cH
    cQ
    cG
    ctrls
    cfv
    #
    wbr
    wph
    vx
    cP
    cQ
    cS
    cF
    cG
    cH
    cI
    cN
    cV
    crctcsh.v
    crctcsh.i
    crctcsh.d
    crctcsh.n
    crctcsh.s
    crctcsh.h
    crctcsh.q
    crctcshwlk
    wph
    cF
    cI
    cdm
    #
    cword
    wcel
    #
    cF
    ccnv
    wfun
    #
    cS
    cz
    wcel
    #
    w3a
    #
    cH
    cF
    cS
    ccsh
    co
    wceq
    @0
    wph
    @3
    @4
    wa
    #
    @5
    @6
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    cP
    @1
    wbr
    #
    @7
    crctcsh.d
    cP
    cF
    cG
    crctistrl
    @8
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    cF
    wf1
    #
    @7
    cP
    cF
    cG
    cI
    crctcsh.i
    trlf1
    @11
    @10
    @2
    cF
    wf
    #
    @4
    wa
    @7
    @10
    @2
    cF
    df-f1
    @12
    @3
    @4
    @2
    @9
    cF
    iswrdi
    anim1i
    sylbi
    syl
    3syl
    wph
    cS
    cc0
    cN
    cfzo
    co
    wcel
    @5
    crctcsh.s
    cS
    cc0
    cN
    elfzoelz
    syl
    @3
    @4
    @5
    df-3an
    sylanbrc
    crctcsh.h
    @2
    cS
    cF
    cH
    cshinj
    mpisyl
    cQ
    cH
    cG
    istrl
    sylanbrc
end
