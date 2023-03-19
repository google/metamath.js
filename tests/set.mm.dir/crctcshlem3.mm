include "cvv.mm"
include "wcel.mm"
include "ccrcts.mm"
include "cfv.mm"
include "wbr.mm"
include "ctrls.mm"
include "crctistrl.mm"
include "cwlks.mm"
include "w3a.mm"
include "trliswlk.mm"
include "wlkv.mm"
include "simp1.mm"
include "3syl.mm"
include "ccsh.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "cle.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt.mm"
include "mptex.mm"
include "3jca.mm"

theorem crctcshlem3
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
  assume crctcsh.v: |- V = ( Vtx ` G )
  assume crctcsh.i: |- I = ( iEdg ` G )
  assume crctcsh.d: |- ( ph -> F ( Circuits ` G ) P )
  assume crctcsh.n: |- N = ( # ` F )
  assume crctcsh.s: |- ( ph -> S e. ( 0 ..^ N ) )
  assume crctcsh.h: |- H = ( F cyclShift S )
  assume crctcsh.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )

  disjoint N x
  assert |- ( ph -> ( G e. _V /\ H e. _V /\ Q e. _V ) )

  proof
    wph
    cG
    cvv
    wcel
    #
    cH
    cvv
    wcel
    #
    cQ
    cvv
    wcel
    #
    wph
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    @0
    crctcsh.d
    cP
    cF
    cG
    crctistrl
    @3
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    @0
    cF
    cvv
    wcel
    #
    cP
    cvv
    wcel
    #
    w3a
    @0
    cP
    cF
    cG
    trliswlk
    cP
    cF
    cG
    wlkv
    @0
    @4
    @5
    simp1
    3syl
    3syl
    @1
    wph
    cH
    cF
    cS
    ccsh
    co
    cvv
    crctcsh.h
    cF
    cS
    ccsh
    ovex
    eqeltri
    a1i
    @2
    wph
    cQ
    vx
    cc0
    cN
    cfz
    co
    #
    vx
    cv
    #
    cN
    cS
    cmin
    co
    cle
    wbr
    @7
    cS
    caddc
    co
    #
    cP
    cfv
    @8
    cN
    cmin
    co
    cP
    cfv
    cif
    #
    cmpt
    cvv
    crctcsh.q
    vx
    @6
    @9
    cc0
    cN
    cfz
    ovex
    mptex
    eqeltri
    a1i
    3jca
end
