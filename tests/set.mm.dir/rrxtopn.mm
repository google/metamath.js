include "crrx.mm"
include "cfv.mm"
include "ctopn.mm"
include "cds.mm"
include "cmopn.mm"
include "cbs.mm"
include "crefld.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csqrt.mm"
include "cmpt2.mm"
include "cfrlm.mm"
include "ctch.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "rrxval.mm"
include "syl.mm"
include "fveq2d.mm"
include "cvv.mm"
include "ovex.mm"
include "tchtopn.mm"
include "ax-mp.mm"
include "a1i.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "rrxds.mm"
include "eqtrd.mm"

theorem rrxtopn
  let wph: wff ph
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cV: class V
  let vk: setvar k
  assume rrxtopn.1: |- ( ph -> I e. V )

  disjoint I f
  disjoint I g
  disjoint I x
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint V f
  disjoint V g
  disjoint V x
  disjoint k x
  assert |- ( ph -> ( TopOpen ` ( RR^ ` I ) ) = ( MetOpen ` ( f e. ( Base ` ( RR^ ` I ) ) , g e. ( Base ` ( RR^ ` I ) ) |-> ( sqrt ` ( RRfld gsum ( x e. I |-> ( ( ( f ` x ) - ( g ` x ) ) ^ 2 ) ) ) ) ) ) )

  proof
    wph
    cI
    crrx
    cfv
    #
    ctopn
    cfv
    #
    @0
    cds
    cfv
    #
    cmopn
    cfv
    #
    vf
    vg
    @0
    cbs
    cfv
    #
    @4
    crefld
    vx
    cI
    vx
    cv
    #
    vf
    cv
    cfv
    @5
    vg
    cv
    cfv
    cmin
    co
    c2
    cexp
    co
    cmpt
    cgsu
    co
    csqrt
    cfv
    cmpt2
    #
    cmopn
    cfv
    wph
    @1
    crefld
    cI
    cfrlm
    co
    #
    ctch
    cfv
    #
    ctopn
    cfv
    #
    @8
    cds
    cfv
    #
    cmopn
    cfv
    #
    @3
    wph
    @0
    @8
    ctopn
    wph
    cI
    cV
    wcel
    #
    @0
    @8
    wceq
    rrxtopn.1
    @0
    cI
    cV
    @0
    eqid
    #
    rrxval
    syl
    #
    fveq2d
    @9
    @11
    wceq
    #
    wph
    @7
    cvv
    wcel
    @15
    crefld
    cI
    cfrlm
    ovex
    @10
    @8
    @9
    cvv
    @7
    @8
    eqid
    @10
    eqid
    @9
    eqid
    tchtopn
    ax-mp
    a1i
    wph
    @10
    @2
    cmopn
    wph
    @8
    @0
    cds
    wph
    @0
    @8
    @14
    eqcomd
    fveq2d
    fveq2d
    3eqtrd
    wph
    @2
    @6
    cmopn
    wph
    @6
    @2
    wph
    @12
    @6
    @2
    wceq
    rrxtopn.1
    vx
    @4
    vf
    vg
    @0
    cI
    cV
    @13
    @4
    eqid
    rrxds
    syl
    eqcomd
    fveq2d
    eqtrd
end
