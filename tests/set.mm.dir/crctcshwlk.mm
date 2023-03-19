include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "crctcshlem4.mm"
include "wi.mm"
include "ccrcts.mm"
include "ctrls.mm"
include "crctistrl.mm"
include "trliswlk.mm"
include "3syl.mm"
include "breq12.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "mpd.mm"
include "crctcshwlkn0.mm"
include "pm2.61dane.mm"

theorem crctcshwlk
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
  assert |- ( ph -> H ( Walks ` G ) Q )

  proof
    wph
    cH
    cQ
    cG
    cwlks
    cfv
    #
    wbr
    #
    cS
    cc0
    wph
    cS
    cc0
    wceq
    #
    wa
    cH
    cF
    wceq
    cQ
    cP
    wceq
    wa
    #
    @1
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
    crctcshlem4
    wph
    @3
    @1
    wi
    @2
    wph
    @1
    @3
    cF
    cP
    @0
    wbr
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
    @4
    crctcsh.d
    cP
    cF
    cG
    crctistrl
    cP
    cF
    cG
    trliswlk
    3syl
    cH
    cF
    cQ
    cP
    @0
    breq12
    syl5ibrcom
    adantr
    mpd
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
    crctcshwlkn0
    pm2.61dane
end
