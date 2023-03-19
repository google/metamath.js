include "co.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "tgelrnln.mm"
include "tglinerflx1.mm"
include "tglinerflx2.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"

theorem tghilberti1
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cG: class G
  let cI: class I
  let cL: class L
  let vy: setvar y
  assume tglineelsb2.p: |- B = ( Base ` G )
  assume tglineelsb2.i: |- I = ( Itv ` G )
  assume tglineelsb2.l: |- L = ( LineG ` G )
  assume tglineelsb2.g: |- ( ph -> G e. TarskiG )
  assume tglineelsb2.1: |- ( ph -> P e. B )
  assume tglineelsb2.2: |- ( ph -> Q e. B )
  assume tglineelsb2.4: |- ( ph -> P =/= Q )

  disjoint B x
  disjoint G x
  disjoint I x
  disjoint L x
  disjoint P x
  disjoint Q x
  disjoint ph x
  disjoint B y
  disjoint x y
  disjoint G y
  disjoint I y
  disjoint L y
  disjoint P y
  disjoint Q y
  disjoint ph y
  assert |- ( ph -> E. x e. ran L ( P e. x /\ Q e. x ) )

  proof
    wph
    cP
    cQ
    cL
    co
    #
    cL
    crn
    #
    wcel
    cP
    @0
    wcel
    #
    cQ
    @0
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    cQ
    @4
    wcel
    #
    wa
    #
    vx
    @1
    wrex
    wph
    cB
    cG
    cI
    cL
    cP
    cQ
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tgelrnln
    wph
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tglinerflx1
    wph
    cB
    cP
    cQ
    cG
    cI
    cL
    tglineelsb2.p
    tglineelsb2.i
    tglineelsb2.l
    tglineelsb2.g
    tglineelsb2.1
    tglineelsb2.2
    tglineelsb2.4
    tglinerflx2
    @7
    @2
    @3
    wa
    vx
    @0
    @1
    @4
    @0
    wceq
    @5
    @2
    @6
    @3
    @4
    @0
    cP
    eleq2
    @4
    @0
    cQ
    eleq2
    anbi12d
    rspcev
    syl12anc
end
