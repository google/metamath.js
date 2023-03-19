include "cui.mm"
include "cfv.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cphi.mm"
include "cc0.mm"
include "cif.mm"
include "wss.mm"
include "eqid.mm"
include "unitss.mm"
include "a1i.mm"
include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "dchrf.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cdif.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "wne.mm"
include "adantr.mm"
include "simpr.mm"
include "dchrn0.mm"
include "biimpd.mm"
include "necon1bd.mm"
include "impr.mm"
include "sylan2b.mm"
include "cn.mm"
include "cfn.mm"
include "dchrrcl.mm"
include "znfi.mm"
include "3syl.mm"
include "fsumss.mm"
include "dchrsum2.mm"
include "eqtr3d.mm"

theorem dchrsum
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  let vb: setvar b
  let vc: setvar c
  let cU: class U
  assume dchrsum.g: |- G = ( DChr ` N )
  assume dchrsum.z: |- Z = ( Z/nZ ` N )
  assume dchrsum.d: |- D = ( Base ` G )
  assume dchrsum.1: |- .1. = ( 0g ` G )
  assume dchrsum.x: |- ( ph -> X e. D )
  assume dchrsum.b: |- B = ( Base ` Z )

  disjoint .1. a
  disjoint B a
  disjoint a ph
  disjoint X a
  disjoint Z a
  disjoint a k
  disjoint .1. k
  disjoint a x
  disjoint k x
  disjoint k ph
  disjoint ph x
  disjoint a b
  disjoint a c
  disjoint U a
  disjoint b c
  disjoint b k
  disjoint b x
  disjoint U b
  disjoint c k
  disjoint c x
  disjoint U c
  disjoint U k
  disjoint U x
  disjoint X k
  disjoint X x
  disjoint Z b
  disjoint Z c
  disjoint Z k
  disjoint Z x
  assert |- ( ph -> sum_ a e. B ( X ` a ) = if ( X = .1. , ( phi ` N ) , 0 ) )

  proof
    wph
    cZ
    cui
    cfv
    #
    va
    cv
    #
    cX
    cfv
    #
    va
    csu
    cB
    @2
    va
    csu
    cX
    c.1
    wceq
    cN
    cphi
    cfv
    cc0
    cif
    wph
    @0
    cB
    @2
    va
    @0
    cB
    wss
    wph
    cB
    cZ
    @0
    dchrsum.b
    @0
    eqid
    #
    unitss
    #
    a1i
    wph
    cB
    cc
    cX
    wf
    @1
    cB
    wcel
    #
    @2
    cc
    wcel
    @1
    @0
    wcel
    #
    wph
    cB
    cD
    cG
    cN
    cX
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.d
    dchrsum.b
    dchrsum.x
    dchrf
    @0
    cB
    @1
    @4
    sseli
    cB
    cc
    @1
    cX
    ffvelrn
    syl2an
    @1
    cB
    @0
    cdif
    wcel
    wph
    @5
    @6
    wn
    #
    wa
    @2
    cc0
    wceq
    #
    @1
    cB
    @0
    eldif
    wph
    @5
    @7
    @8
    wph
    @5
    wa
    #
    @6
    @2
    cc0
    @9
    @2
    cc0
    wne
    @6
    @9
    @1
    cB
    cD
    @0
    cG
    cN
    cX
    cZ
    dchrsum.g
    dchrsum.z
    dchrsum.d
    dchrsum.b
    @3
    wph
    cX
    cD
    wcel
    #
    @5
    dchrsum.x
    adantr
    wph
    @5
    simpr
    dchrn0
    biimpd
    necon1bd
    impr
    sylan2b
    wph
    @10
    cN
    cn
    wcel
    cB
    cfn
    wcel
    dchrsum.x
    cD
    cG
    cN
    cX
    dchrsum.g
    dchrsum.d
    dchrrcl
    cB
    cN
    cZ
    dchrsum.z
    dchrsum.b
    znfi
    3syl
    fsumss
    wph
    cD
    @0
    c.1
    cG
    cN
    cX
    cZ
    va
    dchrsum.g
    dchrsum.z
    dchrsum.d
    dchrsum.1
    dchrsum.x
    @3
    dchrsum2
    eqtr3d
end
